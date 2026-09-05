# R5b report: the level descriptions, the ImgArm discharge, and the tower lift

**Date:** 2026-08-03. **Files written:** `src/L/Rud/LevelDesc.lagda.md` (new, 917
Agda code lines, 1,284 file lines) and this report. Nothing else: no `Everything`,
no `Switch`, `Describe`, `Step`, `Ops`, `Images`, `Realize`, and never
`src/L/Rud/Graphs.lagda.md` (the sibling batch's file). No commits, no
`postulate`, no hole, no `TERMINATING`, `--safe` on. Every agda run used
`GHCRTS=-M12g`, one check at a time (C-12).

**Headline.** `Switch.Descr.ImgArm` is **discharged in full at every limit level
of the tower**, for all sixteen operations and all four argument splits, under
one recorded hypothesis (the relativization slot is named inside the level). The
switch's `closure→definable` therefore stands with that hypothesis gone, and the
tower lift is delivered up to the successor of the level index, which is proved
here to be the sharp bound.

**Headline finding (design):** the U-parameter case is **not** a relativization
and does not need one. `FOL.Manipulation.Relativize` cannot be instantiated at
the level (its bound must be a *constant* of the carrier and `U ∉ U`), and it
turns out nothing is lost: at a *rud-closed* level every U-parameter description
is **Δ₀**, obtained by re-binding the offending quantifier **inside the
candidate** instead of inside the level. SZ's Lemma 1.4 lands in `Σ_ω` only
because it works at an arbitrary transitive carrier. Section 5.

**Stop-line:** 1,600 code lines (917 used). The U-parameter block came to ~590
lines against the 600-line pause threshold, so the threshold was approached but
not crossed; section 6 records the measurement.

---

## 1. The per-operation level-description table

All at `U = Jset μ limμ` (`μ` a limit), `sub : Fof i a b ⊆ U`, argument splits
`a, b ∈ U ⊎ ≡ U`. "member arm" means the value is shown to be a **member** of `U`
and `Descr.memArm` (the membership atom) finishes.

| op | value | plain (a,b ∈ U) | U-parameter case | route | formula |
|---|---|---|---|---|---|
| F0 | `{a,b}` | member arm | **no split needed** | subset hypothesis puts both members in `U`, rud closure returns the pair | atom |
| F1 | `a \ b` | member arm | `a ≡ U`: absorb the left conjunct; `b ≡ U`: value is empty | `F1-spec` + transitivity | `¬̇(x ∈̇ b)` / `⊥̇` |
| F2 | `a × b` | member arm | all three splits | **pair descent** | `prDesc Ψ`, `Ψ` the surviving atom or `⊤̇` |
| F3 | `{⟨u,z,v⟩}` | member arm | all three splits | **triple descent** | `trDesc Ψ`, `Ψ = ∃̇∈ b (prAt′ …)` / atom / `⊤̇` |
| F4 | `{⟨u,v,z⟩}` | member arm | all three splits | **triple descent** | as F3, coordinates swapped |
| F5 | `⋃a` | member arm (`F5 a b = F5 a a`) | `a ≡ U`: `⋃U = U` | union fact `Uunion` | `⊤̇` |
| F6 | `dom a` | member arm (via `F6-indep`) | `a ≡ U`: `dom U = U` | pairing closure (`pr v v ∈ U`) | `⊤̇` |
| F7 | `∈ ∩ a×a` | member arm (via `F7-indep`) | `a ≡ U` | **pair descent** | `prDesc (var p ∈̇ var q)` |
| F8 | `{a"{z} : z∈b}` | member arm | `a ≡ U`: every slice is `U`, so a member would be `U`; `b ≡ U`: value is a member of `U` | `sliceU`; `F8-ext` + one LEM spend | `⊥̇` / atom |
| F9 | `pr a b` | member arm | **no split needed** | pair-valued (`pr c d = F0 ⁅c⁆s ⁅c,d⁆`) | atom |
| F10 | `a"{b}` | member arm | `b ≡ U`: empty (`pr U v ∈ U` gives `U ∈ U`); `a ≡ U, b ∈ U`: equals `U` | pairing closure + irreflexivity | `⊥̇` / `⊤̇` |
| F11 | `pr (left b) (pr a (right b))` | member arm | **no split needed, no pairhood case** | pair-valued, always | atom |
| F12 | `pr (left b) (pr (right b) a)` | member arm | **no split needed** | pair-valued, always | atom |
| F13 | `⁅left b , pr (right b) a⁆` | member arm | **no split needed** | pair-valued, always | atom |
| F14 | `⁅left b , pr a (right b)⁆` | member arm | **no split needed** | pair-valued, always | atom |
| F15 | `a ∩ A` | member arm | `a ≡ U`: `U ∩ A` | needs `A` named in `U` (**the one hypothesis**) | `x ∈̇ A` / `⊤̇` |

**Which Relativize pieces carried each case: none.** `relativize`,
`Δ₀-relativize` and `relativize-correct` are not imported by the chapter; see
section 5 for why, and for what took their place.

Machinery shared across the table (all new in this chapter):

- `pairArm` (12 lines) covers **six** operations at once (F0, F9, F11–F14): a
  value of the form `F0 c d` that is a subset of `U` has `c, d ∈ U`, hence is a
  member of `U` by rud closure. No pairhood guard, no junk branch: `F11`–`F14`
  are Kuratowski pairs *by definition*, whatever their second argument is.
- `prDescAt` / `prDescAt-out` / `prDescAt-in` / `prSetArm` (95 lines): the pair
  descent at an arbitrary de Bruijn index.
- `trDesc` / `trDesc-out` / `trDesc-in` / `trSetArm` (75 lines): the triple
  descent, literally the pair descent composed with itself at the index the first
  one produced.
- The pair reader `sglAt′`/`pairAt′`/`prAt′` with `Δ₀-` witnesses and the
  `AtPr` adequacy (57 lines): a **third** verbatim restatement, because the
  coding chapter's and the description chapter's copies are both `private`
  (section 7, lesson candidate 3).
- Tower facts (35 lines): `Utr`, `Urud`, `U∉U`, `prU`, `prL-in-U`, `prR-in-U`,
  `Uunion`, `dne`.

## 2. The ImgArm discharge record

**Verbatim, not reshaped.** The export is

```agda
module At (μ : V ℓ) (limμ : ⟨ isLimit μ ⟩) where
  U = Jset μ limμ
  module Ds = Descr U Utr
  module ImgArmOf (hA : ⟨ A ∈ˢ U ⟩ ⊎ (A ≡ U)) where
    imgArm : Ds.ImgArm
```

`Ds.ImgArm` is `Switch.Descr`'s own type, untouched and unreshaped:

```agda
ImgArm = (i : Op16) (a b : V ℓ)
       → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u)) → (⟨ b ∈ˢ u ⟩ ⊎ (b ≡ u))
       → ((v : V ℓ) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ u ⟩)
       → Σ[ Φ ∈ Formula ⟪ u ⟫ 1 ] (Defu.defSet Φ ≡ Fof i a b)
```

Two things are **conditioned**, both recorded, neither silent:

1. **The carrier is a limit level, not an arbitrary transitive set.** This is the
   D-8-style reshape the brief allowed, and the induction does demand it: the
   plain-argument case *is* the level's rud closure (`Jset-rud`), and three of
   the sixteen level cases (F5, F6, F10) are absorptions that hold only because
   the level is closed under pairing and equal to its own union. At an arbitrary
   transitive `u` those cases are genuinely `Σ_ω` and would need the machinery
   this chapter shows is unnecessary at a level. The discharge is delivered
   exactly where `Switch.LimitSwitch` consumes it, so nothing is lost downstream.
2. **`hA : ⟨ A ∈ˢ U ⟩ ⊎ (A ≡ U)`.** The sixteenth operation is `F15A a = a ∩ A`;
   at `a ≡ U` its description is the membership atom against `A`, which needs `A`
   to have a constant in `⟪U⟫`. This is the amenability side condition the
   relativized hierarchy carries anyway, and the plain trunk instantiates
   `A := ∅`, a member of every level. It is the module's **only** hypothesis.

Every formula produced is Δ₀ and its `Δ₀` witness is built (`described` requires
one), so the discharge is strictly stronger than `ImgArm` asks: the arm's type
allows an arbitrary first-order formula.

## 3. The tower-lift record

Delivered inside `ImgArmOf`:

```agda
memberDef : (x : V ℓ) → ⟨ x ∈ˢ U ⟩ → (x ⊆ U) → ⟨ x ∈ˢ Ds.Defu.Def ⟩
stepDef   : (x : V ℓ) → ⟨ x ∈ˢ step U ⟩ → (x ⊆ U) → ⟨ x ∈ˢ Ds.Defu.Def ⟩
belowDef  : (γ : V ℓ) → ⟨ γ ∈ˢ μ ⟩ → (x : V ℓ) → ⟨ x ∈ˢ step (Sset γ) ⟩ → ⟨ x ∈ˢ U ⟩
towerDef  : (δ : V ℓ)
          → ((γ : V ℓ) → ⟨ γ ∈ˢ δ ⟩ → (⟨ γ ∈ˢ μ ⟩ ⊎ (γ ≡ μ)))
          → (x : V ℓ) → ⟨ x ∈ˢ Sset δ ⟩ → (x ⊆ U) → ⟨ x ∈ˢ Ds.Defu.Def ⟩
```

The rails are exactly the ones the brief named. `Sset-out` at the stage `δ`
produces an earlier index `γ ∈ δ` with `x ∈ step (Sset γ)`; the bound hypothesis
(`δ ⊆ sucV μ`, written without needing `∈sucV-elim`) splits `γ` into two cases,
and **the limit case is absorption**: for `γ ∈ μ`, `limit-succ-mem` and
`Sset-suc`/`Sset-mono` put `x` inside `U` itself, where `Refine`'s membership atom
describes it. For `γ ≡ μ` the member sits in one step over `U` and the one-step
`switch-⊆` applies. No induction on `δ` is needed at all: the stage recursion
does it in one `Sset-out`.

**The R3 residue as stated in the r3c report is not liftable as stated, and this
is a finding, not a shortfall.** That report set the target as
"`x ∈ Jset α` with `x ⊆ Jset β`". That statement is **false** for `α` more than
one block above `β`: `P(J_β) ∩ J_{β+ω·2}` is the collection of subsets of `J_β`
definable over `J_{β+ω}`, which by Tarski's theorem strictly exceeds
`Def(J_β)` (the satisfaction predicate of `J_β` is the standard witness). The
true target is the block `β + ω`, i.e. the ω-iteration of `step` over `U`. This
chapter delivers the block's **first stage** (`δ ⊆ sucV μ`), which is sharp for a
statement about a single stage, and section 4 records exactly what the rest of
the block needs.

**What the rest of the block needs (named, not silent).** At `step (step U)` the
`arm-image` case has arguments in `step U ∪ {step U}`. Three of the four
sub-cases already close from what is proved here (`a, b ∈ U` gives rud closure;
`a = U` is the level case; `a = Fof j c d` with `c, d ∈ U` is again in `U`). The
fourth, where an argument is itself a level-parameter value such as `U \ b`, is
the composition case, and closing it is the same mathematics as SZ's "every
rudimentary function is simple": one needs the composite syntax `Comp` in the
*reverse* direction, reading a member of the ω-block as `F(U, a⃗)` for a single
composite `F` with parameters in `U`. That is a chapter, and it is the same shape
as the standing `Jimg` residue on the other side (r3c §5 R1).

## 4. The improved corollary

Stated beside the old one, in this chapter, with `Switch` untouched:

```agda
closure→definable       : (x : V ℓ) → ⟨ x ∈ˢ step U ⟩ → (x ⊆ U) → ⟨ x ∈ˢ Ds.Defu.Def ⟩
closure→definable-tower : (δ : V ℓ) → (δ ⊆ sucV μ, spelled out)
                        → (x : V ℓ) → ⟨ x ∈ˢ Sset δ ⟩ → (x ⊆ U)
                        → ⟨ x ∈ˢ Ds.Defu.Def ⟩
```

Against `Switch.LimitSwitch.closure→definable`, which reads
`Ds.ImgArm → (x : V ℓ) → ⟨ x ∈ˢ step Ju ⟩ → (x ⊆ Ju) → ⟨ x ∈ˢ Def Ju ⟩`, the
improvement is: **the `ImgArm` hypothesis is gone**, traded for `hA` (one
`⊎`-valued fact about the relativization slot, trivial in the plain trunk) and
for the carrier being a limit level (which `LimitSwitch` already fixes). The
tower version is new. Both are exports of `L.Rud.LevelDesc.At.ImgArmOf`.

Note the corollary is stated at a *single* level index `μ`, not at the pair
`(α, β)` of `LimitSwitch`: the subset direction never needed the bigger level,
only the ⊇ direction does.

## 5. Why Relativize does not enter, and what took its place

The brief pointed at `FOL.Manipulation.Relativize` as the standing candidate, so
here is the read and the verdict.

`relativize c φ` tightens `∃̇`/`∀̇` to `∃̇∈ (con c)`/`∀̇∈ (con c)`, `Δ₀-relativize`
certifies the result, and `relativize-correct` pins `γ ⊨ relativize c φ` to the
companion semantics `γ ⊨ᴬ φ` with `A = ι c`. Every piece is exactly what the
U-parameter case wants **except one**: the bound enters as a *constant* `c : K`
of the formula's constant domain. In `DefOf U` the constant domain is `⟪ U ⟫`,
whose inhabitants denote **members** of `U`, and `U ∉ U` by regularity. So there
is no `c` with `ι c = U`, and the operator has no instance at the level. (The
chapter's own prose says as much: "A bound that is a proper class has no constant
to stand on"; the level is not a proper class, but from inside `⟪ U ⟫` it is
indistinguishable from one.)

Two further routes were priced and both rejected:

- Instantiate `Correct` at `K = V ℓ`, `ι = id`, `c = U`. This works and gives
  `⊨ᵁ`, but it produces a formula over the constant domain `V ℓ` mentioning
  `con U`, which cannot be relabelled into `Formula ⟪ U ⟫ 1`, the type `ImgArm`
  demands.
- Write the U-parameter formulas with unbounded `∃̇`/`∀̇` and lean on `defSet`'s
  inner semantics (`⊨ᵐ` over `𝒮ᵥ ↾ M`), where unbounded quantifiers *already*
  range over the members of `U`, so `defSet` of an arbitrary formula is literally
  `Σ_ω` over `⟨U, ∈⟩`. This is sound and needs no constant, but it costs a new
  induction (inner satisfaction against the ambient bounded companion, `abs₀`
  extended past Δ₀) because `Chain.chain` and hence `Descr.described` require a
  Δ₀ witness.

**What was done instead.** At a level neither is necessary. The offending
quantifier in each U-parameter description ranges over a *component of the
candidate*: in `U × b` the left component `p` of `v = pr p q` satisfies
`p ∈ ⁅p⁆s ∈ v`; in `∈ ∩ U×U` both components do; in `F3`/`F4` the three
components sit two and four membership steps inside `v`. Since `defSet` makes `v`
range over members of `U` and `U` is transitive, "the component lies in `U`" is
free, and the quantifier is re-bound **inside `v`**, which is a bounded
quantifier. So the description stays Δ₀, `chain` applies, `described` applies,
and no semantics work is needed at all. The two remaining side conditions are
handled the same way: "this component lies in the member argument" is an atom,
and "this pair lies in the level" is discharged by pairing closure.

This is the chapter's mathematical departure from SZ 1.4, and it is a
strengthening: at a rud-closed level, `P(U) ∩ step(U) ⊆ Δ₀-Def(U)`, not merely
`⊆ Σ_ω-Def(U)`.

## 6. Timings, and the stop-line measurement

| stage | wall clock |
|---|---:|
| stage 1 (tower facts, `Arm`/`reshape`, pair-valued six, F1, F5, F6, F10, F15) | 1.9 s |
| + the pair reader restatement | 2.0 s |
| + pair descent frame, F2 (3 cases), F7, F8 at the level-in-first-slot | 3.1 s |
| + tower lift and improved corollary | 3.2 s |
| + generalized frame `prDescAt` (refactor, F2/F7 untouched) | 3.3 s |
| + triple descent frame, F3 (3 cases), F4 (3 cases) | 5.1 s |
| + F8 at the level-in-index-slot (`F8-ext`, one LEM spend) | 5.3 s |
| **final whole-file cold check** | **5.6 s** |
| gates (`lint-prose`, `lint-agda`, `check-glossary`, `weave-i18n`) | all exit 0 |

**No wall, no heap event, no check above 6 s, nothing killed.** Every check ran
under `GHCRTS=-M12g`, one at a time.

**Stop-line accounting.** 917 code lines against 1,600. The U-parameter portion,
counted as the pair reader (57) + pair descent frame (95) + triple descent frame
(75) + the U branches of F1/F5/F6/F10/F15 (~95) + F2/F7 instances (~95) + F3/F4
instances (~120) + F8's two level cases (~130) minus the shared member-arm lines,
comes to roughly **590 lines against the 600-line pause threshold**. The
threshold was approached but never crossed, so the batch ran to completion; had
F8's index-slot case needed the extra-point construction to be spelled as a
separate operation it would have crossed, and the pause would have been called
there.

## 7. Surprises and lesson candidates

1. **(D series, new) A closure hypothesis on the carrier is worth more than a
   description chapter.** The brief anticipated "the sixteen instantiations and
   their dispatch on `Op16` are not assembled (mechanical, but bulky)". They were
   never assembled and never needed to be: at a rud-closed carrier the whole
   plain-argument half of `ImgArm` is `Jset-rud` followed by `memArm`, one line
   per operation. The bulky per-operation instantiation of `Describe`'s sixteen
   `FᵢDesc` modules (with F8's slice-closure hypothesis, F11–F14's `y ≡ pr a b`
   hypothesis, and F15's predicate slot) is **entirely avoided**. Measured: the
   plain half is 16 dispatch lines plus one 12-line helper; the anticipated route
   would have been several hundred. Rule: before instantiating a delivered
   description at a carrier, ask whether the carrier's own closure already puts
   the value inside it.

2. **(D series, new) The junk branch you feared may not exist: read the operation
   before the specification.** `F11`–`F14` were expected to need a pairhood case
   split with the images chapter's junk lemmas (`right-nonpair`,
   `left-⋂-collapse`, `left-⋂-empty`) and the excluded middle, exactly as
   `Step.trans-F11` does. But `F11 x y = pr (left y) (pr x (right y))` is a
   Kuratowski pair *definitionally*, junk arguments or not, so a value that is a
   subset of the carrier has both its members inside and the closure returns it.
   Four operations, zero case splits, zero classical spend. The specification
   `F11-spec` quantifies over the pair decomposition and invites the split; the
   *definition* makes it unnecessary.

3. **(C series, new) A three-times-restated helper is a delivery defect, not a
   coincidence.** `prAt′` and its adequacy have now been written three times in
   this tree: `L.Coding.Base` (over its own constant domain), `L.Rud.Describe`
   (over an arbitrary domain, `private`), and here (over an arbitrary domain,
   again, because the description chapter's copy is `private`). Cost this batch:
   57 lines and no risk, but the third copy is the signal. The remedy is not a
   fourth copy: the arbitrary-domain reader belongs in a shared chapter, and the
   description chapter's `private` block should be its consumer. Recorded rather
   than acted on, since `Describe` is out of this batch's write scope (R-36).

4. **(reading of the R3 residue, corrected) A residue can be stated at a target
   that is false.** r3c §5 R3 asked to lift `switch-⊆` to "`x ∈ Jset α` with
   `x ⊆ Jset β`". That statement fails by Tarski for `α ≥ β+ω·2`, so the residue
   as recorded was not a gap in the proof but a mis-stated target. The
   liftable statement is bounded by one block, and this batch delivers its first
   stage with the bound explicit in the type. Lesson: when a batch records a
   residue, record the *statement* it intends, and price its truth before the
   next batch prices its proof.

5. **(craft) Generalizing a working frame from "at the free variable" to "at an
   index" cost nothing and bought the hardest two operations.** `prDesc` was
   written first at the free variable and proved; generalizing it to `prDescAt k`
   (the target term becomes `var k`, shifted by the four binders) was a
   mechanical edit, kept `prDesc` as `prDescAt zero` with the F2/F7 consumers
   untouched, and made the triple descent literally `prDescAt zero (prDescAt d0 Ψ)`
   with its `out`/`in` a two-line composition. F3 and F4, six cases in total,
   then went green on the first check. All the de Bruijn arithmetic that would
   have been hand-written in an eight-binder formula lives in one 20-line
   definition instead.

6. **(measurement) The classical spend of this chapter is one, and it is in the
   last case.** Only `F8` with the level in the index slot uses `lem` (deciding
   whether some index in the level has an empty slice, and the double negation
   that follows). Everything else, including all four `⊥̇` cases and the two
   descent frames, is constructive given the tower facts. That is one spend
   against the D-7 budget's expectations, and it sits in a case the classical
   text does not even isolate.

## 8. Protocol compliance

- Files created: `src/L/Rud/LevelDesc.lagda.md` and `_build/r5b-report.md`.
  `git status` shows exactly `?? src/L/Rud/LevelDesc.lagda.md` beside the sibling
  batch's `?? src/L/Rud/Graphs.lagda.md`, which was never opened.
- `Everything`, `Switch`, `Describe`, `Step`, `Ops`, `Images` unmodified; only
  the module itself was typechecked, never `make check` in full. The four Python
  gates were run directly on the new file and all exit 0.
- `GHCRTS=-M12g` on every run, one at a time; no wall, no heap exhaustion, no
  kill.
- Prose: en + zh, no em dash, CJK full-width punctuation, half-width parens,
  zh paragraphs on single lines; `初步函数` is the only rendering used for
  rudimentary function.
- Stop-lines respected: 917 / 1,600 total; U-parameter portion ~590 / 600.
</content>
