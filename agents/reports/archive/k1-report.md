# L3.31-R5-K1 report: the base block, hereditary finiteness at Sset ω

Batch: the base-block chapter (`src/L/Rud/BaseBlock.lagda.md`) and this report.
Scope honoured: nothing else was touched (in particular `src/Everything.lagda.md`
is unmodified; registration of the chapter in the import list is left to the
owner, as the scope did not include it). Wall protocol: every check ran under
`GHCRTS=-M8g`, one check at a time; there was no heap-exhausted exit and no
180 s event. Deps were already compiled by `make check`'s `Everything`, so each
incremental check of the chapter was a single-module recompile at ~1.3 s warm
(the final measurement; the source edits in between each stayed under 12 s).
D-10 was discharged by the recon (the statement is true in the delivered
indexing); this batch prices the witness.

## 1. Per-deliverable table

| # | deliverable | names | code lines | timing | notes |
|---|---|---|---|---|---|
| 1 | `isLimit ω` | `limω` (`ω-not-zero`, `ω-not-succ`) | 12 | < 1 s | both missing halves: `ω ≢ ∅` via `#∈ω zero`; non-successor via the numeral characterization of the predecessor plus `∈-irrefl` |
| 2 | S-side tally | `module Sside` (`up`, `name`, `imgItem`, `op16`/`op16Onto`, `stepItem`, `stepTally`) + `sTally` | 198 | ~1 s | induction on the step's finite square: tally of `u ∪ {u}`, Fin-indexed square enumeration (`FinSumChar`/`FinProdChar`), the sixteen images read only through the sealed `step-in-img` surface |
| 3 | finite-member lemma | `finSetMem` (finSet-table form) + `finiteMember` (Tally form), with `finSet0∅`, `finSetSuc`, `Sset-zero-∅`, `∅∈Ssetω`, `op-in-J`/`opF0`/`opF5` | 119 | ~1 s | engine: `Jset-rud ω limω` (the limit level closes under F0/F5), singleton ∪ tail realized as `F5 (F0 (F0 h0 h0) X)` |
| 4 | power obligation | `module Power` (`carrier`, `part-in-J`, `fam`, `defPow≡finSet`, `defPow∈J`) + `basePow` | 49 | ~1 s | (a) subsets of the finite carrier are finite and definable (FinOf/`PowerStep` machinery), (b) collected by `finSetMem`, (c) the collection is itself a `finSet` of members of `Sset ω` |
| 5 | base-block instance | `baseDefPow`, `baseStage∈J`, `baseFragment` | 25 | < 1 s | `ζ ∈ ω` is merely a numeral; the `γ = ω` instance in the shape DefInJ's discharge consumes, plus the identity-fragment witness at that point |

Total: 453 code lines in 624 file lines (STOP-LINE 700 kept, including
imports). The recon's calibration was 200-400 code lines; the overshoot is
entirely the S-side tally line-item (198 lines), which the recon's estimate
left unpriced ("Tally (Sset (# n)) ... are small"). The rest (12 + 119 + 49 +
25 = 205) lands inside the calibrated band.

## 2. How the base case plugs into DefInJ

`DefInJ.Discharge.defStage∈J` has the shape

```
defStage∈J : (ζ γ : S) → ⟨ isLimit γ ⟩ → ⟨ ζ ∈ˢ γ ⟩ → ⟨ Lset ζ ∈ˢ Sset γ ⟩
           → ⟨ Lset (sucV ζ) ∈ˢ Sset γ ⟩
```

and its proof spends the module parameter `frag : DefFragment`, a function of
`(ζ, γ, limγ, ζ∈γ, L∈)` producing a bounding-fragment witness. The base
chapter closes the missing point:

- `limω : ⟨ isLimit ω ⟩` is the first argument at `γ := ω` (deliverable 1).
- `baseStage∈J ζ ζ∈ω L∈` **is** `defStage∈J ζ ω limω ζ∈ω L∈`'s conclusion:
  `⟨ Lset (sucV ζ) ∈ˢ Sset ω ⟩`, proved outright via `Lset-suc` (the same
  successor collapse DefInJ spells `Lsuc≡Def`) and the power obligation.
- `baseFragment ζ ζ∈ω L∈` is the point-instance of the `DefFragment` input
  that `Discharge` would need at `(ζ, ω, limω, ζ∈ω, L∈)`: the identity
  fragment `F = 𝒟ₒ (Lset ζ)`, with `F ∈ Sset ω` supplied by `baseDefPow` and
  the two containment directions reflexive.

The sharpened `LimitFragment` form is deliberately absent: `ω` has no limit
below it, and the recon already records that the sharpened form is refutable
there. The plug-in is therefore not "instantiate `Discharge`'s module
parameter" (that needs a fragment for every `γ`) but "supply the discharge's
conclusion at `γ = ω`", which `baseStage∈J`/`baseFragment` do in the exact
type shapes DefInJ's exports read. If a future batch wants the generic
machinery rerun at `ω` (e.g. to exercise `Sstage₂`/`Sep` at the first limit),
`baseFragment` is the witness `Discharge`'s `frag ζ ω limω ζ∈ω L∈` expects.

## 3. Ported pattern vs built fresh

Ported (established, imported or copied per pattern):

- `Tally` (the record), `stageOrder` (the L-side carrier tally), and
  `PowerStep` (`part`/`part-def`/`part-mask`, `maskOf`, `maskCount`/`maskAt`/
  `mask-onto`) from `L.Choice.Finite`, the L-side twin; `FinOf`'s
  `finSet∈𝒟ₒ` is consumed inside `PowerStep` exactly as delivered.
- `FinSumChar.Equiv`/`FinProdChar.Equiv` (cubical library): the index
  arithmetic for sums and products of `Fin`, the generalization of the Finite
  chapter's hand-rolled `joinFin`/`splitFin`.
- `ext-⊆` (2 lines, copied from DefInJ's own), `Sset`-tower surface and
  `Jset-rud` from the Rud chapters.

Built fresh (the S-side content the recon priced):

- `limω` and its two missing conjuncts.
- The whole S-tower tally: `u ∪ {u}` tally, the square enumeration at the
  `Fin` index, the sixteen-op enumeration (`op16`/`op16Onto` over the
  constructors `op0..op15`), the step tally, and the `sTally` induction.
- The finite-member lemma: the table lemma by induction on the length, with
  the extensional equality between the `finSet` table and the
  `F5 (F0 ...)` composite, and the Tally-form corollary.
- The power module's S-side reading (`part-in-J`, `defPow≡finSet`,
  `defPow∈J`) and the base instance.

The engine `Jset-rud ω limω` is imported, but this is its first consumer at
`ω`; the report's "(b) via the step's F0/pair arms and the finite union" is
realized as the limit level's closure under F0 and F5, which is `Jset-rud`'s
whole content at the first limit.

## 4. Lesson candidates (for the owner's ledger)

1. **The hProp-join double-truncation trap** (extends I-2): `⟨ P ⊔ Q ⟩` is
   already the truncation `∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁` (Logic's `_⊔_ =
   ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥ₚ`). Wrapping an `F0-spec`-style `.fst` result in
   `PT.rec` double-truncates, and the failure prints as a confusing
   plain-sum-vs-truncation mismatch. Cure: apply the join-valued function
   directly and do the `PT.rec` inside the consumer, at the plain-sum level.
   Measured: three ~10 s checks in this batch.
2. **Step's `f0..f15` aliases are definitions, not constructors**: using them
   as enumeration patterns fails with `Op16.op0 != f0`; the reliable patterns
   are the constructors `op0..op15`. Extends the P-a tag-discipline family.
3. **`Sset-zero` is not exported by `L.Rud.Step`**: the hierarchy
   instantiation exports the other case equations but not `Sset ∅ ≡ ∅`, so
   the bottom of the tower cost a 6-line local proof (`Sset-zero-∅`).
   Candidate: export it from Step, or record the derivation.
4. **R-35/P-c applied before a wall (second instance of R-38's prophylactic
   datum)**: the square and the sixteen images are enumerated at the `Fin`
   index, memberships are read only through the sealed step surface, and the
   whole chapter ran at 1.3 s warm with no wall event. The `-- perf:` marker
   on `module Sside` names the discipline.
5. **R-37 held**: no lemma statement carries a transported membership at a
   concrete `Sset (sucV β)`; the `sTally (suc n)` record rebuilds membership
   fields with `subst` inside the body (Finite's own pattern), and the
   `∅ ∈ Sset ω` proof goes through the local `Sset-zero-∅` rather than a
   transport-heavy statement.
