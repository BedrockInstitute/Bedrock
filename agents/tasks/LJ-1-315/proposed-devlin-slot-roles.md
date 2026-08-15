# PROPOSED DIGEST, not yet landed

**This file is a PROPOSAL.** Task `[LJ-1.315]` wrote it in
`agents/tasks/LJ-1-315/`. The orchestrator lands it, or does not, into
`dev/literature/`. **A digest is canonical only inside `dev/literature/`, and
nothing is canonical twice (DD19).** Suggested landed name:
`dev/literature/level-formula-slot-roles.md`.

---

# The level-hood formula: arity, what it binds, what stays free

**The question.** How does each author state "`v` is the `γ`-th level of `L`"
as a formula? How many slots does the formula use? Which does it bind? Which
stay free, and in what roles?

**Why the corpus needs this.** `dev/literature/devlin-II5.md` carries Devlin's
level-hood chain and its complexity requirements. **It does not carry the slot
arithmetic**, and a port that numbers its variables needs the slot arithmetic.
Task `[LJ-1.312]` refuted a Bedrock formula's slot roles by machine, and this
digest is the outside view beside that measurement.

**Sources and status.** Devlin, Jech and Schindler-Zeman are read from the
scans already in `_build/literature/`. Kunen 1980 was fetched on 2026-08-15
from `https://fa.ewi.tudelft.nl/~hart/onderwijs/set_theory/Jech/Kunen-1980-Set_Theory.pdf`,
open access, and was NOT retained in the tree. **`dev/literature/BIBLIOGRAPHY.md`
entry 17 lists Kunen as cite-only, and this fetch changes that.**

## 1. The table

| # | Source | The statement | Arity | Binds | Free | Roles | Locator |
|---:|---|---|---:|---|---|---|---|
| 1 | Devlin 2.4 | `D(v,u) = ∃w[K(w,u) ∧ C(w,v,u)]`, and `D(v,u) ↔ v = Def(u)` | 2 | `w`, ONE bound, DETERMINED by `K(w,u)` | `v`, `u` | VALUE, ARGUMENT | `_build/literature/dev2.txt:619-623` |
| 2 | Devlin 2.6 | `G(f,α) = ∃w[K(w, ⋃ran(f)) ∧ F(w,f,α)]`; `G` says `f = (L_γ ∣ γ ≤ α)` | 2 | `w`, ONE bound, determined | `f`, `α` | SEQUENCE, ORDINAL | `_build/literature/dev2.txt:655-659` |
| 3 | Devlin 2.7 | `H(x,α) = ∃f[G(f,α) ∧ (x = f(α))]`; `H` says `x = L_α` | 2 | `f`, and `w` inside `G` | `x`, `α` | **VALUE, ORDINAL** | `_build/literature/dev2.txt:679-680` |
| 4 | Devlin 5.2 (a) | `Φ(z,v,γ)` with `∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]` | 3 in `Φ`, ONE closed | `z` at position 0 | `v` at 1, `γ` at 2 | **VALUE, ORDINAL** | `_build/literature/dev2.txt:1186-1191` |
| 5 | Devlin 5.2 (b) | `(∀γ<α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z,v,γ)]` | same | `z` | `v`, `γ` | **VALUE, ORDINAL** | `_build/literature/dev2.txt:1193-1198` |
| 6 | Jech 13.14 | "The function `α → L_α` is Δ₁", from a Σ₁ step `∃W[...]` | 2 | `W`, the approximating function | value, ordinal | **VALUE, ORDINAL** | `_build/literature/jech13.txt:561-572` |
| 7 | Jech 13.13 | A Π₂ SENTENCE `σ`: `(M,∈) ⊨ σ` iff `M = L_δ` for a limit `δ` | **0** | everything | nothing | level-hood is a property of the CARRIER | `_build/literature/jech13.txt:605-614` |
| 8 | Kunen VI 3.2 | "The function `L(α)` is absolute for transitive models of ZF - P" | 2, IMPLICIT | **no formula written** | value, ordinal | **VALUE, ORDINAL** | Kunen 1980, Ch. VI section 3, Lemma 3.2; the printed page number is not recoverable from the extraction |
| 9 | Schindler-Zeman 1.10(2) | "`x = S_γ^A` is Σ₁ over `J_α^A` as witnessed by a formula which does not depend on `α`" | 2 | not exhibited | `x`, `γ` | **VALUE, ORDINAL** | `_build/literature/sz-full.txt:322-323` |

## 2. The three laws the table states

### 2.1 The free pair is the VALUE and the ORDINAL, in every source

Rows 3, 4, 5, 6, 8 and 9 agree. **A level-hood formula leaves exactly the two
slots its conclusion uses.** No source leaves anything else free.

### 2.2 ONE bound binds ALL the unbounded quantifiers

Devlin states this in words, twice.

> We now seek a bound for all the unbounded quantifiers in `B(v,u)`.
> (`_build/literature/dev2.txt:590-591`)

> Hence, all unbounded quantifiers in `B(v,u)` can (without loss of meaning) be
> bound by the set `K(u) = ...`
> (`_build/literature/dev2.txt:600-601`)

> ... all the unbounded quantifiers which figure in `E(f,α)` ... can be bound by
> the set `K(⋃ran(f))`.
> (`_build/literature/dev2.txt:655-656`)

**No source uses two independent bounds.** A formula with two independent bound
slots has no precedent in rows 1 to 9.

### 2.3 The bound is DETERMINED, not chosen

Devlin's `∃w` carries the conjunct `K(w,u)`, "which says `w = K(u)`"
(`_build/literature/dev2.txt:611`). **So the witness is unique.** A port that
closes its bound with a bare existential states "SOME bound works" where Devlin
states "THE canonical bound works". **Those are different statements.** This
digest records the difference and does not settle whether it matters.

## 3. Jech's second presentation, and why it is not a disagreement

Jech row 7 makes level-hood a property of the CARRIER: a transitive `M` is a
level exactly when `M ⊨ σ`, for one Π₂ SENTENCE `σ` with no free slots
(`jech13.txt:605-614`). Jech row 6 gives the Δ₁ function `α → L_α`, whose
relation carries Devlin's free pair.

**Jech carries BOTH shapes, and neither leaves a bound free.** This is D-26's
dichotomy at the level formula, and `dev/literature/devlin-II5.md:296-310`
records it from the same texts.

## 4. Kunen writes no formula, and that is the useful fact

Kunen defines the definable powerset as a SET (Definition VI 1.1, printed page
165) and proves absoluteness by an appeal to a general recursion theorem
(Lemma VI 3.2, citing IV 5.6; its printed page number is not recoverable from the extraction). **IV 5.6 argues by transfinite
induction inside the model and exhibits no formula.**

**So the textbook that Paulson's Isabelle/ZF development follows never writes an
object-level level-hood formula.** A port that writes one is doing something the
textbook does not do, and it owns the slot bookkeeping alone.

## 5. What no formalization does

`dev/literature/formalizations.md` and
`dev/literature/formalizations-landscape.md` searched Isabelle/ZF, Lean
mathlib4, Flypitch, Mizar, Metamath, Coq and Naproche. **The one system with
`L` is Isabelle/ZF**, and it builds `L` from a recursion over `DPow`
(`dev/literature/formalizations.md:41-45`). `DPow` is a function, so its
existentials are set-theoretic and not numbered slots.

**MEASURED, within that corpus: no formalization writes an object-level
level-hood formula with numbered free slots.** So no formalization faces a
slot-role question. **INFERRED for the wider claim**, because the sweep is
bounded by the indexes it searched on 2026-08-02.

## 6. A CORRECTION to `dev/literature/devlin-II5.md`

**`devlin-II5.md:95-100` presents Devlin's clause (a) as a quotation from
`dev2.txt:1186-1194`. The scan does not carry clause (a)'s display.** Those
lines print `(a)`, then a bare `V`, then a bare `y`. The digest's clause (a) is
a correct RESTORATION, and the digest's section 6 does not list it among its
restorations.

**The restoration is confirmed by three legible facts**, so no re-fetch is
needed:

1. `dev2.txt:1186` prints the slot order: "Σ o formula Φ (z, ι;, γ) of LST".
2. `dev2.txt:1193-1198` prints clause (b) with the same free pair.
3. `dev2.txt:679-680` prints 2.7's `H(x,α) = ∃f[G(f,α) ∧ (x = f(α))]`.

**Action for a later editor:** add clause (a) to `devlin-II5.md` section 6 as a
resolved restoration, with these three confirmations.

## 7. What this digest does NOT say

1. It does not say whether any Bedrock formula is correct. That is a probe's
   job.
2. It does not settle whether an undetermined bound is sound (section 2.3).
3. It does not survey formalizations beyond the six systems that
   `formalizations-landscape.md` searched on 2026-08-02.
4. It reads Devlin, Jech and Schindler-Zeman through OCR or PDF extractions.
   Every load-bearing line was checked for sense against its surrounding prose.

## 8. Sources

| source | status | locator |
|---|---|---|
| Devlin, "Constructibility", Ch. II, sections 2.2 to 2.7 and 5.2 | **READ** | `_build/literature/dev2.txt:585-693`, `:1180-1200` |
| Jech, "Set Theory" 3rd ed., Ch. 13 | **READ**, the level-formula parts | `_build/literature/jech13.txt:555-625` |
| Kunen, "Set Theory: An Introduction to Independence Proofs", 1980 | **READ**, Ch. VI sections 1 and 3, Ch. IV Theorem 5.6 | fetched 2026-08-15 from `https://fa.ewi.tudelft.nl/~hart/onderwijs/set_theory/Jech/Kunen-1980-Set_Theory.pdf` |
| Schindler and Zeman, "Fine structure", Lemma 1.10 | **READ** | `_build/literature/sz-full.txt:310-330` |
| `dev/literature/formalizations.md` | **READ** whole | in repo |
| `dev/literature/formalizations-landscape.md` | **READ** whole | in repo |
| Jensen 1972; Zeman, "Inner Models and Large Cardinals" | **POINTER-ONLY** | `dev/literature/BIBLIOGRAPHY.md:141-144`, `:151-153` |
