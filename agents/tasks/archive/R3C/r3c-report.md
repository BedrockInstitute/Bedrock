# R3c report: the switch theorem, the basis discharge, and the two named residues

**Date:** 2026-08-03. **Files written:** `src/L/Rud/Switch.lagda.md` (new,
911 Agda code lines), `src/L/Rud/Ops.lagda.md` (append-only R-36 appendix,
+54 Agda code lines / +68 file lines), and this report. Nothing else: no
`Everything`, no `Realize`, `Describe`, `Step`, `Hierarchy`, `Images`,
`OrdArith`, and no `Order` (the parallel R4 batch's file). No commits, no
postulate, no hole, no `TERMINATING`, `--safe` on. Every agda run used
`GHCRTS=-M12g`, one check at a time (C-12).

**Headline.** The abstract basis telescope is discharged at the concrete
sixteen-function basis, so the realization induction now runs over the real
operations and `realizeC` is a theorem about `F0`..`F15`. The five reverse
hops the description chapter recorded as walled are closed. The switch
theorem is proved in both directions as far as the delivered machinery
reaches, with the constant-content gap **closed** and exactly **two named
residues** standing, both stated as explicit module hypotheses in the code,
never silently.

**Stop-line:** 1,800 for Switch (911 used) plus 200 for Ops (54 used). The
image construction that was priced to pause at 600 came in at 67 lines as a
*construction*; its **closure property** is the residue, and its shape is
recorded in section 6.

---

## 1. The discharge table

`L.Rud.Realize.Basis` has eighteen parameters (nine operations, nine
specifications) and `Eval` one more (the stack-indexed image), with the image
specification a parameter of the inner `Realize`. All are discharged.

| telescope slot | concrete supplier | code lines | notes |
|---|---|---:|---|
| `pairOp` | `F0` | 0 | the basis function itself |
| `pairSpec` | `F0-spec` across the `∈ˢ`/`∈ₛ` bridge | 5 | |
| `diffOp` | `F1` | 0 | |
| `diffSpec` | `F1-spec` | 12 | `⟨ ¬ P ⟩` is `⟨P⟩ → Empty.⊥`, no `rec*` |
| `interOp` | `F1 a (F1 a b)` | 3 | sealed `opaque` |
| `interSpec` | `diffSpec` twice + `dne` | 17 | **the one LEM spend** (D-7) |
| `prodOp` | `F2` | 0 | |
| `prodSpec` | `F2-read` / **`F2-write`** + `prAsF0` | 40 | |
| `memOp` | `F7 a a` | 3 | sealed |
| `memSpec` | `F7-read` / **`F7-write`** + `prAsF0` | 42 | |
| `unionOp` | `F5 a a` | 3 | sealed |
| `unionSpec` | `F5-spec` | 18 | |
| `colOp` | `F10 (F7 s s ∩ ({a} × b)) a`, `s = {a} ∪ b` | 12 | sealed |
| `colSpec` | `F7-read/write`, `F2-read/write`, `F10-spec`, `pr-inj` | 52 | |
| `chSepOp` | `condOp (memWit a b) c` | 3 | sealed |
| `chSepSpec` | `condSpec` + `memWit-out/in` | 12 | |
| `eqSepOp` | `condOp (eqWit a b) c` | 3 | sealed |
| `eqSepSpec` | `condSpec` + `eqWit-out/in` | 12 | |
| `imgOp` (`Eval`) | `sett ⟪p⟫ (λ m → evalC f (⟪p⟫↪ m ∷ vs))` | 3 | see section 6 |
| `imgSpec` (`Realize`) | `sett` membership + `eval-agree` | 27 | |

Shared machinery inside the same sections: `prAsF0` (2), `sUnion` + its two
membership lemmas (11), `colGraph` (2), `condOp`/`condSpec` (34),
`memWit`/`out`/`in` (48), `eqWit`/`out`/`in` (33), `evalC` (12),
`eval-agree` (14), the two membership bridges and `dne` (10).

**The three genuinely new constructions** (none of them a single basis
function):

1. **Collection** `colOp a b = {y ∈ b : a ∈ y}`. Take `s = {a} ∪ b`, cut the
   membership relation `F7 s s` down to `{a} × b`, and read the slice at `a`
   with `F10`, whose specification `(v ∈ F10 x y) ≡ (pr y v ∈ x)` is the
   cleanest hop in the whole layer (a path, not a pair of implications).
2. **The conditional set** `condOp t c = F6 (c × t)`, the domain of a product:
   it is `c` when `t` has a member and `∅` otherwise. Both separations are one
   instance each, so the two spend one construction, not two. The two tests
   are `memWit a b = F7 {a,b} {a,b} ∩ {⟨a,b⟩}` (inhabited iff `a ∈ b`) and
   `eqWit a b = {a} ∩ {b}` (inhabited iff `a = b`).
   The earlier plan for `condOp` went through `F5 (F8 (c × t) t)` and the
   small-index `F8-spec`; `F6` of the product replaces it at a third of the
   cost and needs no fibre bookkeeping.
3. **The image** (section 6).

## 2. The imgOp design record

`imgOp` is the only telescope slot whose value has to agree with the very
evaluation it sits inside: `Eval.eval (imgC f a) ws = imgOp f ws (eval a ws)`
and `imgOp f vs p` must be `{ eval f (y ∷ vs) : y ∈ p }`. Three designs were
weighed; the delivered one is the third.

- **Mutual recursion** `evalC`/`imgOpC`. Works on paper (the call matrix
  descends), but pays a mutual-block termination check and gains nothing.
- **Define `imgOpC` first.** Impossible: it needs the evaluation.
- **Delivered: inline the image at its own constructor.** `evalC` is written
  first, with
  `evalC (imgC f a) ws = sett ⟪ evalC a ws ⟫ (λ m → evalC f (⟪ evalC a ws ⟫↪ m ∷ ws))`,
  and `imgOpC f vs p = sett ⟪ p ⟫ (λ m → evalC f (⟪ p ⟫↪ m ∷ vs))` is read off
  that clause, so `evalC (imgC f a) ws ≡ imgOpC f ws (evalC a ws)` holds by
  `refl`. No mutual block, structural recursion in the composite, 12 + 3 lines.

`Eval` is then instantiated at `imgOpC`. Its own `eval` is a *different*
function with the same clauses, so `eval-agree : Ev.eval c ws ≡ evalC c ws`
is proved by a ten-clause path-lambda induction (14 lines), and `imgSpecC`
(27 lines) bridges through it: the sett index `⟪ p ⟫` is a **small index**
throughout (R-35), the forward direction reads the fibre, the backward one
plants it with `∈-asFiber`.

**The image's closure property is not built.** See section 6.

## 3. The reverse-read inventory

Appended to `src/L/Rud/Ops.lagda.md`, R-36 pattern exactly: five new
`opaque unfolding` blocks, one per sealed operation, nothing existing
changed, renamed or unsealed.

| lemma | type | body |
|---|---|---|
| `F2-write` | `∥ Σ p q. p∈a × q∈b × x ≡ₕ pr p q ∥₁ → x ∈ˢ F2 a b` | repack + `F2-spec .snd` |
| `F3-write` | `∥ Σ u z v. z∈a × pr u v∈b × x ≡ₕ pr u (pr z v) ∥₁ → x ∈ˢ F3 a b` | same |
| `F4-write` | `∥ Σ u v z. z∈a × pr u v∈b × x ≡ₕ pr u (pr v z) ∥₁ → x ∈ˢ F4 a b` | same |
| `F6-write` | `∥ Σ u v. pr u v∈a × x ≡ₕ u ∥₁ → x ∈ˢ F6 a b` | same |
| `F7-write` | `∥ Σ u v. u∈a × v∈a × u∈v × x ≡ₕ pr u v ∥₁ → x ∈ˢ F7 a b` | same |

Each body is one line: inside the seal the sealed right-hand side `Fᵢ-RHS`
unfolds to the transparent nested `⋁`, so the only work is repacking the
read's *flat* decomposition into the RHS's *nested* one. The r3b2 no-go trail
was right that no external route exists and right about the remedy; the cost
of the remedy is 54 lines.

**Closures stated in Switch** (`module Hops`, 84 lines), with `Describe`
untouched. For each of F2, F3, F4, F6, F7:

- `Fᵢ-DRHS-mem : ⟨ Fᵢ-DRHS a b v ⟩ → ⟨ v ∈ˢ Fᵢ a b ⟩` — the recorded NO-GO cell
  itself, closed;
- `Fᵢ-desc-out : ⟨ (v ∷ []) ⊨ Φᵢ ⟩ → ⟨ v ∈ˢ Fᵢ a b ⟩` — composed with
  `Describe`'s own `Fᵢ-sat-out`.

With these, all five descriptions are adequate in **both** directions.
`Describe` needed no edit at all (`F6Desc` takes the transitivity parameter,
so `Hops` carries one too). Note r3b2's separate finding still stands and is
untouched by this: the plain `defSet Φᵢ ≡ Fᵢ a b` equations for F2/F3/F4/F7
are *false*, not merely sealed, because those images are not subsets of the
carrier; the power-set intersection in the switch statement is exactly what
kills those cells, and that is why the ⊆ direction below is stated for `x`
with `x ⊆ u` and never as a bare equation.

## 4. The switch statement, as proved

Everything below is in `module Switch {ℓ} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ)`.

**The realization side, concrete** (unconditional):

```agda
realizeC : (u : V ℓ) (tu : Trans u) (φ : Formula ⟪ u ⟫ 1) → Δ₀ φ
         → Σ[ c ∈ Comp 0 ] (Ev.eval c [] ≡ DefOf.defSet u φ)
```

`Comp` and `Ev.eval` are now the composite syntax and evaluation over the
sixteen basis functions.

**The constant-content certificate** (unconditional, `module WalkCon`):

```agda
realizeCon : (φ : Formula ⟪ u ⟫ 1) (d : Δ₀ φ) → ConIn P (realizeC u tu φ d .fst)
```

for any predicate `P` with `P u` and `P` holding on members of `u`. This was
*not* in the brief's plan and is the batch's one unforeseen necessity: the
delivered `realize` says nothing about the constants it plants, and the
closure induction asks exactly that. It is proved by re-running the walk's own
recursion (10 formula clauses, 4+4+2 view grids), which is possible only
because `Realize`'s clause helpers are transparent.

**The closure side** (`module Closure J Jrud`, then `module Eval-J Jimg`):

```agda
evalC-in-J : (c : Comp k) (ws : Vec (V ℓ) k)
           → ConIn InJ c → AllIn InJ ws → ⟨ evalC c ws ∈ˢ J ⟩
switch-⊇   : (φ : Formula ⟪ u ⟫ 1) (d : Δ₀ φ)
           → ConIn InJ (realizeC u tu φ d .fst) → ⟨ DefOf.defSet u φ ∈ˢ J ⟩
```

with nine of the ten constructors discharged from `Jset-rud` alone
(`J-F0`…`J-F10` wrappers through `Fof-fᵢ`, then `J-inter`, `J-union`, `J-mem`,
`J-col`, `J-cond`, `J-memWit`, `J-eqWit`, `J-chSep`, `J-eqSep`, each in its own
`opaque unfolding` block), and `Jimg` the single hypothesis.

**The description side** (`module Descr u utrans`):

```agda
described : (x : V ℓ) (Φ : Formula ⟪ u ⟫ 1) → Δ₀ Φ
          → (x ⊆ u) → (desc-in) → (desc-out on u) → DefOf.defSet Φ ≡ x
memArm    : x ∈ u → x ⊆ u → Σ[ Φ ] (defSet Φ ≡ x)      -- discharged
selfArm   : Σ[ Φ ] (defSet Φ ≡ u)                       -- discharged
switch-⊆  : ImgArm → (x : V ℓ) → ⟨ x ∈ˢ step u ⟩ → (x ⊆ u) → ⟨ x ∈ˢ DefOf.Def u ⟩
```

`described` is the shape the whole ⊆ direction runs on and the place the
power-set intersection does its work: `x ⊆ u` is a hypothesis, the two
adequacy directions are hypotheses, and the conclusion is the *equation*
`defSet Φ ≡ x` that r3b2 showed is false without the subset condition.

**The trunk-facing corollary** (`module LimitSwitch α limα β limβ β∈α`), with
`Ju = Jset β limβ` and `Jα = Jset α limα`:

```agda
definable→closure : (φ : Formula ⟪ Ju ⟫ 1) (d : Δ₀ φ) → ⟨ DefOf.defSet Ju φ ∈ˢ Jα ⟩
closure→definable : Ds.ImgArm → (x : V ℓ) → ⟨ x ∈ˢ step Ju ⟩ → (x ⊆ Ju)
                  → ⟨ x ∈ˢ DefOf.Def Ju ⟩
```

`definable→closure` sits inside `module Up Jimg` and is otherwise
unconditional: transitivity of `Ju`, `Ju ∈ Jα` and `Ju ⊆ Jα` all come from
the tower (`Sset-trans`, `Sset-mem`, `Sset-mono`), and the constants
certificate discharges `ConIn` on the spot.

## 5. Residue against SZ Lemma 1.4, stated explicitly

SZ 1.4 reads `P(U) ∩ rud_A(U ∪ {U}) = P(U) ∩ Σ_ω^{⟨U,∈,A⟩}`. Against that:

**R1. The rud image principle (`Jimg`).** The ⊇ inclusion needs every
composite value to land in a closed level. Nine constructors are chains of
`F0`..`F15`; the tenth, the image of a composite family, is *not* a chain of
them term-by-term. The classical fact is SZ Lemma 1.3(b) ("if `F` is rud so is
`(x, ȳ) ↦ F"x`"), whose proof strengthens the induction to the **graph**
`H(p, v̄) = {⟨y, F(y, v̄)⟩ : y ∈ p}` and then extracts with `⋃ F8(H, p)`,
because `F10(H, z) = {F(z, v̄)}`. Two facts were established while scoping it,
and they are why it is a chapter and not a lemma:

- the base case `F(y) = y` demands the identity relation `Id_p = {⟨y,y⟩ : y ∈ p}`
  as a rud function of `p`, and the obvious routes (`p × p` cut by an equality
  test; the singleton image `{{y} : y ∈ p}`, which would give `Id_p = S(S(p))`)
  are each circular in the image operation being built;
- the composition case needs the *join* of two graphs on their common first
  coordinate, which is again not a term-by-term chain.

`Jimg` is therefore a module parameter with the exact type the induction
consumes, and it is the one thing between this chapter and an unconditional
⊇ inclusion. Estimated as its own batch, not a patch.

**R2. The image arm of the descriptions (`ImgArm`).** The ⊆ inclusion needs,
for a value `F_i(a,b) ⊆ u` with `a, b ∈ u ∪ {u}`, a formula over `⟪u⟫`. The
description chapter delivers per-operation formulas at a carrier `A` with the
arguments **members of `A`**. Two gaps:

- the sixteen instantiations and their dispatch on `Op16` are not assembled
  (mechanical, but bulky: F8 carries a slice-closure hypothesis, F11-F14 carry
  a `y ≡ pr a b` hypothesis, F15 carries the predicate slot);
- **the `U`-parameter case is not covered at all.** When `a = u`, the constant
  `con mₐ` does not exist, and SZ's own statement absorbs this by landing in
  `Σ_ω` rather than `Δ₀`: over `⟨U,∈⟩` the atom `w ∈ U` is `⊤` and `∃w ∈ U`
  becomes an unbounded quantifier. Our `DefOf.Def` is the full first-order
  face, so the target is right; what is missing is the syntactic
  relativization of each `Φᵢ` replacing a `u`-constant by unbounded
  quantification, plus its semantic lemma. This is a real piece of design, not
  bookkeeping, and it is why `ImgArm` is a hypothesis rather than an unfinished
  case split.

**R3. One step versus the whole closure.** `switch-⊆` is stated at `step u`
(one application of the operator). Lifting it to `x ∈ Jset α` with `x ⊆ Jset β`
needs the tower induction (`Sset-out` gives `δ ∈ α` with `x ∈ step (Sset δ)`,
and `Sset δ` is not `Jset β`), which is a further step this chapter does not
take. The ⊇ direction has no such gap: it lands in `Jα` directly.

**Not residues (settled here).** The `A`-relativization slot is carried by
`Step`'s `F15A`/`Fof f15` and needs nothing extra from this chapter; the
constants gap is closed; the D-7 intersection spends LEM once, exactly as
ruled, and nowhere else in the basis layer (the walk's own two spends are
`Realize`'s, unchanged).

## 6. Timings, and the one wall

| item | wall clock |
|---|---:|
| Ops with the five write lemmas | 1.6 s |
| Switch stage 1 (bridges, pair, diff, union, inter) | 1.2 s |
| Switch stage 2a (`prAsF0`, prod, mem) | 27.5 s (includes Step rebuild) |
| Switch stage 2b (collection, conditional set, both separations) | 1.7 s |
| Switch stage 3 (image, `Eval`, `eval-agree`, `realizeC`) | **hang, killed at >400 s** |
| the same after sealing (bisected cure) | 3.7 s |
| + closure machinery | 4.1 s |
| + reverse hops (`Describe` first build) | 11.3 s, then 5.8 s |
| + description side | 6.5 s |
| + limit corollary and recap | 6.7 s |
| + constant-content certificate | 8.8 s |
| **final whole-file cold check** | **8.8 s** |
| gates (`lint-prose`, `lint-agda`, `check-glossary`, `weave-i18n`) | all exit 0 |

**The wall, and its bisect (P-i).** Adding `eval-agree` hung the file
(>400 s, killed twice, ~675 MB resident, no error). Bisect, one probe at a
time: `module Bs = Basis …` alone 2.6 s; `evalC` + `imgOpC` 2.8 s;
`module Ev = Bs.Eval imgOpC` 3.1 s; `Ev.eval` reduction probes 3.2 s;
`eval-agree`'s `interC` clause alone 3.2 s; **`eval-agree`'s `colC` clause
alone: hang.** Cause: `colOp` was a transparent definition ending in
`F10`, which `Images` leaves transparent and whose body is
`sett (Σ[ m ∈ ⟪x⟫ ] ⟨ pr y (right (⟪x⟫↪ m)) ∈ₛ x ⟩) …` — a `⋃`/`⋂`-tower under
a `sett` index. The path-lambda endpoint check forced it to normalize at
every clause. **Cure:** seal every derived operation `opaque` at its birth
site with its specification inside the same block (nine blocks:
`interOp`, `unionOp`, `memOp`, the `colOp` cluster, `condOp`, `memWit`,
`eqWit`, `chSepOp`, `eqSepOp`). Whole file 3.7 s, and every later addition
stayed under 9 s. This is P-c and P-i [B] applied one layer *above* where the
tower lives: the tower is in an imported operation, and the consumer's own
alias is what must be sealed.

No heap exhaustion, no exit 137/251, no other check above 30 s.

## 7. Surprises and lesson candidates

1. **(P series, new) Seal a derived alias of a transparent imported operation
   before it can appear under a path lambda.** `P-c` says seal an operation
   whose *index* carries a `⋃`-tower at its birth site. The tower here belongs
   to `Images.F10`, which is transparent and out of reach; what walled was my
   own `colOp = F10 (…) a`, a definition with no tower in sight. Measured:
   `eval-agree`'s `colC` clause alone hangs past 200 s with `colOp`
   transparent; with the nine derived operations sealed the whole 911-line file
   checks in 8.8 s. Rule: when a consumer names a composite of an imported
   operation it does not own, the consumer's alias is a birth site and gets the
   seal. Corollary for the trunk: `L.Rud.Images.F10` (and the `left`/`right`
   pair kit) are transparent by delivery and are a standing hazard for every
   future consumer.
2. **(craft) A path lambda is a normalization request.** `λ i → op (p i) (q i)`
   looks cheaper than `cong₂ op p q` and is, for the elaborator, an endpoint
   check that forces `op` to whnf at both ends. All ten `eval-agree` clauses
   are path lambdas; nine were free and one was fatal, and the difference was
   purely whether `op` was sealed.
3. **(D series, new) An exported theorem that hides a certificate its only
   consumer needs is an interface bug, and the cure may be free.**
   `realize` exports `Σ[ c ] (eval c [] ≡ defSet φ)` and drops the walk's
   `Sub`/`ChrP` certificates and says nothing about `c`'s constants; the
   closure induction needs precisely the constants. Because `Realize`'s walk
   and its clause helpers are ordinary transparent definitions, the certificate
   was recoverable *from outside* by re-running the same recursion (78 lines,
   green first try). Had the walk been sealed, the only cure would have been an
   edit to `Realize`. Lesson: transparency of a syntax-directed recursion is an
   interface asset; seal the heavy *values*, not the syntax walk.
4. **(D series) `F6` of a product is the cheap conditional set.** The planned
   route to "keep `c` if `t` is inhabited" was `F5 (F8 (c × t) t)`, which needs
   `F8`'s small-index specification and fibre bookkeeping. `F6 (c × t)`, the
   domain, is the same set for 34 lines with two reads and two writes. Both
   separations then share it, so the sixteen-function basis pays once for what
   looked like two constructions.
5. **(reading of r3b2's falsity finding, confirmed in the proof)** The reason
   the plain `defSet Φᵢ ≡ Fᵢ a b` equations are false is exactly the reason the
   switch statement carries `P(u) ∩ _` on both sides: `described` takes `x ⊆ u`
   as a hypothesis and could not be stated without it. The junk cells are killed
   by the hypothesis, not by a case analysis.
6. **(measurement, against the r3a walls report)** The r3a A/B/C experiment
   found face abstraction to be insurance rather than medicine. This batch is
   the complementary datum for the *basis* abstraction: instantiating the
   basis telescope at the concrete operations costs 2.6 s and is entirely
   harmless **provided the concrete operations are sealed**. The abstraction
   did not protect against the wall; the seal did.

## 8. Protocol compliance

- Files created/modified: `src/L/Rud/Switch.lagda.md`, the granted append-only
  appendix in `src/L/Rud/Ops.lagda.md`, and `_build/r3c-report.md`. `git status`
  shows exactly `M src/L/Rud/Ops.lagda.md` and `?? src/L/Rud/Switch.lagda.md`.
  `L.Rud.Order` was never opened.
- Only the module was typechecked, never `Everything`, never `make check` in
  full; the four Python gates were run directly on the two touched files and
  all exit 0.
- `GHCRTS=-M12g` on every run, one at a time; two wall events, both killed with
  `pkill` and bisected per P-i, never rerun blind.
- Prose: en + zh, no em dash, CJK full-width punctuation, half-width parens,
  zh paragraphs on single lines; `初步函数` is the only rendering used for
  rudimentary function.
- Stop-lines respected: Switch 911/1,800; Ops appendix 54/200; the image
  construction 67 lines against a 600-line pause threshold.
