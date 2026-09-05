# review-of-approx-in-K: the obligation is FALSE, and this file is the stop

**VERDICT: NO-GO.** `approx-in-K` is not delivered, and it is not
delivered because **it cannot be**. The statement the brief names is
refuted in the tree, at `agents/tasks/LJ-1-532/Probe532.agda:206-209`,
exit 0.

    ApproxInK-is-false : ApproxInK → Empty.⊥

The brief's own stop condition names this case: "If it is not, name what
`g` is built from and STOP". `g` is built from nothing, and the section
below says exactly what that means.

## THE STATEMENT THAT IS REFUTED

`agents/tasks/LJ-1-532/Probe532.agda:108-117`, the brief's type at the
site's own environment:

    ApproxInK =
        (α : V ℓ) → IsLimit α
      → ∀ {n} (b K : Fin n) (γ : S ^ n)
      → fst (lookup K γ) ≡ Lset α
      → IsOrd (fst (lookup b γ))
      → ⟨ fst (lookup b γ) ∈ fst (lookup K γ) ⟩
      → (g : S)
      → ⟨ (g ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
      → ⟨ fst g ∈ fst (lookup K γ) ⟩

**EVERY FRAME FACT THE CHAIN CARRIES IS A HYPOTHESIS HERE.** `K` is a
LIMIT level, the domain bound is an ORDINAL, and the bound lies IN `K`.
The refutation does not win by dropping one of them. The spelling
`⟨ (g ∷ γ) ⊨ ApproxAt zero (suc b) ⟩` is the site's own: `LsetGraphAt w b
= ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w) (suc b) zero)`
(`src/L/Coding/Sequence.lagda.md:291-292`).

## WHY IT IS FALSE

**`ApproxAt` SPEAKS ONLY ABOUT THE KURATOWSKI-PAIR MEMBERS OF `g`.**
`ApproxAt f a = domAt f a ∧̇ ∀̇ (∀̇ (appAt … ⇒̇ Step …))`
(`src/L/Coding/Sequence.lagda.md:286-289`). `domAt`
(`src/L/Coding/Model.lagda.md:278-280`) constrains `x` only through
`inDomAt`, which is "there merely is `y` with `pr x y ∈ f`"
(`src/L/Coding/Model.lagda.md:269-270`). The step conjunct is guarded by `appAt`, which is the same
pair membership (`:289`). **A member of `g` that is not a pair is
unconstrained, and the tree puts no bound on it.**

**THE COUNTEREXAMPLE, IN THREE OBJECTS.** `Probe532.agda:170-193`.

| object | value | why it is admissible |
|---|---|---|
| `K` | `Lset ω` | `ω-IsLimit`, `Probe532.agda:92-97` |
| the bound | `∅` | `∅-ord` (`src/L/Ordinal.lagda.md:77`), and `∅ ∈ Lset ω` at `Probe532.agda:195-197` |
| `g` | `⁅ ω ⁆s` | `sglʟ ωʟ`, an element of the class carrier (`src/L/Coding/InL.lagda.md:363-364` with `ω∈L`, `src/L/Axioms/Infinity.lagda.md:66`) |

`⁅ ω ⁆s` IS an approximation on `∅` (`blind`, `Probe532.agda:191-193`).
Both halves of `domAt` and the step condition are vacuous, and each is
vacuous for a stated reason: no member of `⁅ ω ⁆s` is a Kuratowski pair
(`no-pair-in-g`, `:179-181`, from `ord-not-pr`, `:131-153`), and no set
is a member of `∅`.

`⁅ ω ⁆s` is NOT in `Lset ω` (`sgl-ω∉Lω`, `Probe532.agda:202-203`):
`Lset ω` is transitive (`Lset-layer` with `layer-trans`,
`src/L/Constructible.lagda.md:246` with `:183`), and `ω ∉ Lset ω` because
`ord∈Lset→∈` (`src/L/Ordinal/Stages.lagda.md:265-268`) would put `ω` in
`ω`, against `∈-irrefl` (`src/V/Hierarchy.lagda.md:155-156`).

**THE INSTANCE IS CHEAP BUT THE DEFECT IS NOT LOCAL.** `∅` only makes
the completeness half of `domAt` vacuous as well. At any ordinal bound,
the same junk member can be added to any approximation, because
`ApproxAt` never sees it.

## WHAT TO PUT IN ITS PLACE

**THE ∀-FORM FAILS ONLY ON JUNK.** `Probe532.agda:227-256` proves both
directions: an approximation on an ordinal carries EXACTLY the pairs
that `hierL` carries (`pairs-into-hier`, `:238-244`; `pairs-from-hier`,
`:246-256`). So two approximations on one ordinal differ only in members
that are not pairs, and the refutation says that difference is
unbounded.

**SO ROW SIX'S MEMBERSHIP, CORRECTLY STATED, IS ABOUT THE CANONICAL
WITNESS.** `Probe532.agda:274-277`:

    HierInK = (α : V ℓ) → IsLimit α
            → (β : V ℓ) (hβ : ⟨ isL β ⟩) (oβ : IsOrd β) → ⟨ β ∈ α ⟩
            → ⟨ fst (hierL β hβ oβ) ∈ Lset α ⟩

**IT IS NOT INHABITED HERE AND NOTHING IN THE TREE INHABITS IT.** It is
`[LJ-1.494]`'s measurement: "Is `hierL δ` a member of `Lset α` when `δ`
is? The tree does not bound `hierL δ` by `α`"
(`agents/tasks/LJ-1-494/lj-1.494-report.md:66-67`), with `[LJ-1.230]`
recorded as NO-GO on the same statement before it (`:116-118`, quoting
`agents/tasks/LJ-1-230/lj-1.230-report.md:79`).

**AND THE CORRECTED STATEMENT IS NOT VACUOUS.**
`hier-is-approx` (`Probe532.agda:346-349`) proves the canonical witness
IS an approximation, so `HierInK` is exactly what row six's missing
witness needs and not a statement about an empty class.

## THE ANSWER TO THE BRIEF'S QUESTION

The brief asked whether the two carriers share one obstruction or two.
**THEY SHARE ONE.** Row six at `K` and `[LJ-1.494]`'s stage question are
the same statement about the same object, `hierL`, and the difference
between them is which set is asked to hold it.

## WHAT I DID NOT DO

I did not build row six. I did not touch row seven beyond reading it
(`src/L/BoundedSubset.lagda.md:108-111`). I did not spend either `Σ₁`
certificate: `grep -c "Σ₁-levelHood\|σ₁-up\|Σ₁-Σ₂" Probe532.agda`
returns 0. I postulated nothing: `grep -c postulate` returns 0 in both
Agda files, and both carry `--safe`.
