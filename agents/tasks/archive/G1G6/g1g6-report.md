# G1 + G6 report: ClassJ and the ordinal block map

Goal `[L3.31-R5-G1G6]`. Two new modules, nothing else touched:

- `src/L/Rud/ClassJ.lagda.md` (G1, 37 code lines, 135 file lines)
- `src/L/Rud/OrdBlocks.lagda.md` (G6, 362 code lines, 633 file lines)

Combined code lines: **399** (stop-line 700, respected). Both modules typecheck
clean with `GHCRTS=-M8g`, one check at a time; both pass `lint-agda.py` and
`lint-prose.py` (0 violations). No walls: the longest single check was 45.6 s
(cold), well under the 180 s wall; no heap exhaustion, no exit 137/251.

## 1. G1: ClassJ

Imports only `L.Rud.OrdArith` (committed, for `isLimit`) and `L.Rud.Step`
(the named surface, for `Jset` and `Sset-trans`); it does not touch
`Hierarchy` or any in-flight file directly. The module telescope is
`{ℓ} (lem) (A : V ℓ)`, inherited from `Step`.

### Exports

| Name | Type |
|---|---|
| `isJ` | `S → Ω`, `isJ x = ⋁ S (λ α → (Σ[ lim ∈ ⟨ isLimit α ⟩ ] ⟨ x ∈ˢ Jset α lim ⟩) , isProp…)` |
| `isPropIsJ` | `(x : S) → isProp (⟨ isJ x ⟩)` |
| `Jset→isJ` | `(α : S) → (lim : ⟨ isLimit α ⟩) → (x : S) → ⟨ x ∈ˢ Jset α lim ⟩ → ⟨ isJ x ⟩` |
| `isJ-trans` | `Transitive 𝒮ᵥ isJ` |
| `𝒮ⱼ` | `ZFStructure (hPropAlgebra (ℓ-suc ℓ))`, `𝒮ⱼ = 𝒮ᵥ ↾ isJ` (mirrors `𝒮ʟ`) |

The witness carries the limit certificate `lim : ⟨ isLimit α ⟩`, which subsumes
ordinality (`isLimit-ord`), so the bridge's endpoints line up with `isL`.
Transitivity uses `Sset-trans α` at the unchanged witness `(α , lim , x∈Jset)`,
exactly the `isL-trans` proof shape. Propositionality of the family is
`Σ≡Prop` over the two propositions (`isLimit` hProp-ness, membership hProp-ness).

## 2. G6: OrdBlocks

### Which formulation `b` took, and why

`b` is a **single-equation membership recursion** (`b α = ⋃ { +ω (b δ) | δ ∈ α }`,
sealed `opaque` with `b-compute` as the official unfolding, exactly the tower's
style), with `+ω u = ⋃ { sucIter (suc n) u | n : ℕ }`, the **ω-many
successors' limit** over a `Lift ℕ` index.

Why this combination, measured against the alternative (case-split inside the
recursion via `lem` + `ord-case`):

- **Membership monotonicity becomes free.** `b β ∈ b α` is one step: `b β`
  sits in its own ω-extension (`+ω-mem`), and `+ω (b β)` is a member of the
  family `b α` unions over. No induction, and no ordinality at all: `b-mono`
  and `b-incl` hold for arbitrary indices.
- **The three clauses become theorems instead of definitional cases.**
  `b-zero`, `b-limit`, and `b-suc` are all consequences of one recursion
  clause; the cost is that `b-suc` needs `+ω-mono` on ordinals (one
  `ord-tri` step per successor-inclusion), which is the price the case-split
  design would pay inside every monotonicity and limit proof instead.
- **Ordinality, absorption, and the limit law each close in one or two
  lines** against the delivered ordinal kit (`setUnion-ord`, `suc-ord`).

The alternative (case split on `ord-case` inside `b-step`) makes `b-suc`
definitional but forces every later law through peeled `lem` layers and
ordinal induction; the chosen design keeps the classical content in exactly
three places (see side conditions).

### Exports (block-level)

| Name | Type |
|---|---|
| `b` | `S → S` (opaque), `b = ∈-induction b-step` |
| `b-compute` | `(α : S) → b α ≡ ⋃ (sett ⟪ α ⟫ (λ m → +ω (b (⟪ α ⟫↪ m))))` |
| `b-in` / `b-out` | the two membership directions of `b` (union readings) |
| `b-zero` | `b ∅ ≡ ∅` |
| `b-mono` | `{α β : S} → ⟨ β ∈ˢ α ⟩ → ⟨ b β ∈ˢ b α ⟩` |
| `b-incl` | `{α β : S} → ⟨ β ∈ˢ α ⟩ → b β ⊆ b α` |
| `b-ord` | `(α : S) → IsOrd α → IsOrd (b α)` |
| `b-limit` | `(α : S) → ⟨ isLimit α ⟩ → b α ≡ ⋃ (sett ⟪ α ⟫ (λ m → b (⟪ α ⟫↪ m)))` |
| `b-suc` | `(α : S) → IsOrd α → b (sucV α) ≡ +ω (b α)` |
| `b-absorbs` | `(α : S) → (n : ℕ) → ⟨ sucIter n (b α) ∈ˢ b (sucV α) ⟩` |
| `b-limit-nonzero` | `(α : S) → IsOrd α → ((α ≡ ∅) → ⊥) → ⟨ isLimit (b α) ⟩` |

### Supporting exports (ω-extension)

`sucIter : ℕ → S → S`, `sucIter-ord`, `+ω : S → S`, `+ω-in`, `+ω-out`,
`+ω-mem`, `+ω-sup`, `+ω-iter`, `+ω-ord`, `sucV-mono-ord`, `sucIter-incl`,
`+ω-mono`, `suc-⊆`, `+ω-limit : (u : S) → IsOrd u → ⟨ isLimit (+ω u) ⟩`.
Private: `ix∈`, `limit-succ-mem` (re-derived: `Hierarchy` is in flight),
`limit-block-limit`.

### The laws' table (sizes and timings)

All laws live in one module, so per-law typecheck time is not separately
measurable without fragmenting the file; the honest figure is the module's
**cold check, 45.6 s** (final clean run; identical at ~45-46 s across the
last four full runs). Sizes are code lines including their local helpers
where the helper exists only for that law.

| Law | Lines | Note |
|---|---|---|
| `b-zero` | 10 | via `b-out` + `∅-empty` |
| `b-mono` / `b-incl` | 1 + 1 | free (see above); `+ω-mem`/`+ω-sup` 2 lines |
| `b-ord` | 6 | `∈-induction` + `setUnion-ord` |
| `b-limit` | 24 | union-reading machinery both directions |
| `b-suc` | 8 | + `sucV-mono-ord` 8, `sucIter-incl` 3, `+ω-mono` 5 |
| `b-absorbs` | 1 | + `+ω-iter` 1 |
| `b-limit-nonzero` | 5 | + `+ω-limit` 26, `limit-block-limit` 26 (private) |

### Side conditions the laws honestly need (D-10)

Sanity-checked at small cases in a comment in the file: `b ∅ = ∅`;
`b 1 = +ω ∅ = ω`; `b 2 = +ω ω = ω·2`; `b ω = ⋃ { ω·n | n } = ω²`; all
nonzero blocks are limits. Honest conditions:

- `b-suc` needs `IsOrd α`. `b` is total (`b α = ∅` off the ordinals), but the
  successor clause is an ordinal statement: the collapse of the below-members
  needs `+ω-mono` on ordinals.
- `b-limit` needs `isLimit α`. At a successor the right-hand union omits the
  fresh block `+ω (b α)`; at zero both sides are empty but no limit
  certificate exists to state the equation under; at **limits of limits** the
  equation survives, because `sucV δ ∈ α` and the block at `sucV δ` is a
  genuine extension of the block at `δ` (this is the "limit of limits" subtlety
  recorded: the equation is not false there, but its proof needs the
  successor-closure fact at every member).
- `b-limit-nonzero` needs `α ≢ ∅`: `b ∅ = ∅` is not a limit.
- `+ω-mono` needs both arguments ordinal (`u ⊆ v` alone is not enough; the
  successor operator is not subset-monotone in general, D-8).
- `b-mono`, `b-incl`, `b-zero`, `b-absorbs` are unconditional.

Classical content, in total: (1) `limit-succ-mem` (via `ord-tri`), (2) the
`ord-tri` step inside `sucV-mono-ord` (hence `+ω-mono`, hence `b-suc`), (3)
one `lem` for "a nonzero limit has a member" in `limit-block-limit`'s
nonemptiness. Everything else, including both not-a-successor arguments, is
constructive. The not-a-successor proofs use only `∈sucV-elim` and ordinal
transitivity.

## 3. LESSONS applied

- **P-c**: `b` sealed `opaque` at birth with `b-compute` as the official
  unfolding; consumers read it through `b-in`/`b-out` only.
- **I-2**: every hProp expression in a signature codomain is wrapped in
  `⟨_⟩`; `isLimit` hProps are named through `⟨ … ⟩`.
- **I-3**: every binding inside the `opaque` block carries a type signature.
- **D-8**: monotonicity is membership-shaped (`b-mono`), and in this design it
  costs nothing; the subset form `b-incl` is a corollary.
- **D-10**: the small-case sanity check and honest side conditions are
  recorded in a comment at the law section, before the proofs.
- **R-34**: universe levels pinned explicitly (`Lift {ℓ-zero} {ℓ} ℕ`); no
  `using`-import was left with an open level.
- **C-11**: module body indentation follows the existing top-level pattern;
  parameters stay in scope through the whole body (both files typecheck).

## 4. Surprises

1. **`b-mono` needs no ordinality at all.** In the single-equation design,
   `β ∈ α → b β ∈ b α` holds for every pair of indices, constructively, with
   no induction: the block at `β` is a member of its own ω-extension, which is
   a member of the family `b α` unions over. The brief's law is delivered
   stronger than stated. Lesson candidate: "membership-monotonicity of a
   union-of-extensions family is a family-member argument, not an induction".
2. **The `∈∈ₛ` direction trap.** The small/big membership equivalence
   (`a ∈ b ⇔ a ∈ₛ b`) has `.fst` big→small and `.snd` small→big; one fibre
   step in `+ω-out` was initially written the wrong way and only the error
   text exposed it. Lesson candidate: annotate `∈∈ₛ` direction usage in the
   style sheet.
3. **`∈sucV-elim`'s motive must live in `Type (ℓ-suc ℓ)`** (P-series): the
   not-a-successor branches needed the `⊥*`/`rec*` lift pattern, exactly as
   `limit-succ-mem` in `Hierarchy` does.
4. **`subst` direction discipline.** Four of the early errors were the same
   flip: `subst P p` moves `P x → P y` along `p : x ≡ y`, and in membership
   rewrites one must decide whether the path acts on the element or the level.
   Lesson candidate: spell `P` and the path endpoints explicitly in block
   equalities.
5. **`b-limit` needed `limit-succ-mem` re-derived** because `Hierarchy` is in
   flight and cannot be imported; the proof is a verbatim re-derivation from
   the ordinal kit (15 lines), and the bridge will use `Hierarchy`'s copy at
   the block indices.
6. **The nonemptiness of a limit block is genuinely classical.** `α ≢ ∅`
   does not constructively yield a member `δ ∈ α`; the excluded middle is
   spent exactly there (the only `lem` use in the module beyond `ord-tri`).

## 5. Walls

None. No check exceeded 180 s (max 45.6 s), no heap cap was hit, no exit
137/251. The brief's heap discipline (`GHCRTS=-M8g`, one check at a time) was
followed on every run.
