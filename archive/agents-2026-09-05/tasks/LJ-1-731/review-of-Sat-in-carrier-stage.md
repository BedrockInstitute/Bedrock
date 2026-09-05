# Review of `Sat-in-carrier-stage`: the bound as stated is false

- task: LJ-1.731
- writer: coder
- probe: `agents/tasks/LJ-1-731/Probe731.agda` (typechecks, EXIT=0,
  `runs/p-10.out`)
- discharge: this review states a NO-GO on the obligation's type as the
  brief gave it. Per D-10 the corrected target is recorded beside the
  refuted one, in section 5.

## 1. The target

The brief asks for one term:

    Sat-in-carrier-stage :
        (γ : V ℓ) (oγ : IsOrd γ)
        → ⟨ ω ∈ˢ γ ⟩
        (A : S) → ⟨ fst A ∈ Lset γ ⟩
        {n : ℕ} (φ : Formula S n)
      → ⟨ Sat A φ ∈ˢ Lset γ ⟩

The type quantifies over ALL `φ : Formula S n`. No hypothesis in the
type places the CONSTANTS of `φ`. That is the defect.

## 2. The machine-checked core

`Probe731.agda:108-125` proves `cond-trace-equiv`, generic in a carrier
`B` and an ARBITRARY constant `c` (W2: stated once, at the generic
carrier):

    z ⊨ cond B (var zero ∈̇ con c)
      ≡  ∥ Σ[ v ∈ S ] ( slot-fact(v, z) × ⟨ fst v ∈ fst c ⟩ ) ∥₁

where `slot-fact(v, z)` is `⟨ pr (# zero) (fst v) ∈ fst z ⟩`, the
slot-0 identification. Both directions are one `PT.rec` over the landed
readers `cond∈-out` (`src/L/Coding/Sat.lagda.md:217`) and
`cond∈-in` (`:212`), the term readers `tmIs-var-out` /
`tmIs-var-in` (`src/L/Coding/Sat.lagda.md:92,85`), and the definitional
`≐` clause of the semantics. Membership in the recursion's value for
this formula IS the c-trace of the carrier's values.

## 3. The refutation site

`Probe731.agda:146-161` lands both of the obligation's own hypotheses
at one site:

- γ := `sucV ω`, an ordinal (`Probe731.agda:146-150`), with
  `⟨ ω ∈ sucV ω ⟩` (`:152-153`, from `self∈sucV` in
  `src/V/Model.lagda.md:236`). So `ω ≤ γ` holds, the brief's own guard.
- A := `LsetS ω ω-ord`, with
  `⟨ fst A ∈ Lset (sucV ω) ⟩` (`:160-162`, by `Lset-suc`
  (`src/L/Axioms/Basic.lagda.md:196`) and `𝒟ₒ-intro`).

Take φ := `(var zero ∈̇ con c)` for an arbitrary `c : S`. Then

    Sat A φ = { z ∈ envSet A 1 : z's slot-0 value lies in c }

(the membership is `Sat-mem`, `src/L/Coding/Sat.lagda.md:145-147`;
the condition is section 2's trace). The carrier's values are its own
members, so the trace is the graph-image of `c`'s part over the
carrier.

## 4. Why the trace escapes `Lset γ`

The carrier A = `LsetS ω ω-ord` has `Lset ω` as its underlying set, so
the carrier's values are the hereditarily finite sets and the trace
reads out `d := c ∩ (carrier values)` through the tuple coding. The
slot projection is definable: from a definable trace, `d` is definable
by the bounded formula "the decoded slot value lies in the trace".
Every member of `Lset (sucV ω)` outside `Lset ω` is a definable subset
of `Lset ω` (`Lset-suc`, `src/L/Axioms/Basic.lagda.md:196`: the stage
IS `𝒟ₒ (Lset ω)`, the definable subsets of `Lset ω`). So a trace in
`Lset (sucV ω)` would make `d` a definable subset of `Lset ω`. Choose
`c` so that `d` is not one: such `c` exist because `𝒟ₒ (Lset ω)` holds
only countably many subsets while the carrier's members carry
uncountably many subsets of themselves; formally, `d` may be any subset
of `ω` first appearing at an arbitrary later stage, and
`Lset (sucV ω) = 𝒟ₒ (Lset ω)` contains only the `ω`-definable ones.
For that `c`, the trace is not in `Lset (sucV ω) = γ`, and the
obligation's conclusion is false at a site where both of its
hypotheses hold.

The refutation does not consume `envSet-in-carrier-stage` and is not
repaired by it: the trace argument never uses where `envSet A 1`
sits. (The landed supply-side bound,
`envSetNumeral∈` at `src/L/Coding/Key.lagda.md:486-489`, places
`envSet B n` at `Lset (sucIter 4 σ)` from `ω ∈ σ`; the obligation's
conclusion is about `Sat A φ`, a different set.)

## 5. D-10: the corrected target, recorded beside the original

The false generality is the unplaced constant. The consumer named by
premise 3 never needs it: `src/L/Coding/Powerset.lagda.md:502-506`
feeds `Sat A (toS ψ)`, and `toS ψ`'s constants are carrier members.
For carrier-member constants the landed bridge chapter already reads
the value
(`Adequate`, `src/L/Coding/Bridge.lagda.md:295-299`: membership in
`Sat B (mapFo intoL φ)` is the inner satisfaction `δ ⊨ᴮ φ`), and the
route to the corrected target is:

1. From the hypothesis `envSet-in-carrier-stage`, untruncate a stage
   `δ ∈ γ` with `envSet A n` definable over `Lset δ`
   (`Lset-out` + `Lset-suc`).
2. Merge in the stages of `A` and of `ω` by trichotomy
   (`ord-tri`, `src/L/Ordinal/Linear.lagda.md:136`); the merge stays in `γ`
   because the max of two members of an ordinal is one of them.
3. Induct on `φ`, carrying the inner-world defining formulas as data
   (substituting `con (Sat a)` by the recursion's own formula for `a`,
   and `con B` by `A`'s defining formula), with the adequacy theorem
   per clause. The witness placement the bridge needs is FORCED by the
   hypothesis: every member of `envSet A n` lies in `Lset δ`
   (`𝒟ₒ∋⊆`), sub-value members are `envSet` members
   (`Sat-mem`'s first conjunct), term witnesses are slot members
   (section 2's own reading), and numerals land by
   `ord∈Lset-suc` (`src/L/Ordinal/Stages.lagda.md:434`).
4. Close with `𝒟ₒ-intro` + `Lset-in`.

Corrected target:

    Sat-in-carrier-stage :
        (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ γ ⟩
        (A : S) → ⟨ fst A ∈ Lset γ ⟩
        {n : ℕ} (φ : Formula S (suc n))
        → (consts : every constant of φ has fst in Lset γ)
      → ⟨ Sat A φ ∈ˢ Lset γ oγ ⟩

or, at the consumer's own shape, the same conclusion for
`Sat A (toS ψ)` with `ψ : Formula ⟪ fst A ⟫ n`, no `consts` needed.

Estimated price, from the landed pieces named above: 250 to 450 lines
of Agda, not the brief's 20 to 80. The estimate doubles the brief's
figure because the bridge (step 3) is twelve clauses of reader
plumbing with witness placement, and because the recursion must carry
defining formulas as data through a `PT.rec`.

## 6. What would reopen the original

A formulation that bounds `φ`'s constants (the corrected target), or a
carrier whose value-range cannot see an unplaced constant. The
original unbounded type stays false.
