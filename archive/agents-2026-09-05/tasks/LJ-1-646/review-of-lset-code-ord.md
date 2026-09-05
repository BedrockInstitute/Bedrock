# review-of-lset-code-ord: NO-GO, stated

This file states a NO-GO on the obligation of `[LJ-1.646]`. It is the critic's
input. It does not close the task.

    lset-code-ord : (c : Code) → IsOrd (fst (val c))
                  → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

The term is NOT written. `agents/tasks/LJ-1-646/Probe646.agda` typechecks and
carries the reduction, not the term.

## THE BRIEF'S PREMISE 3 IS WRONG, AND THE EVIDENCE IS ONE TASK OLD

The brief says obstacle two "is exactly this brief's added hypothesis", because
`Lset-only` takes `IsOrd (fst (lookup b γ))` (`src/L/Hierarchy.lagda.md:334`).

`IsOrd` was never the operative obstacle. `Lset-only` is stated at the
CONSTRUCTIBLE-CLASS carrier: `L.Hierarchy` opens `hPropStructure 𝒮ʟ`
(`src/L/Hierarchy.lagda.md:73`) and renames its satisfaction from
`FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans` (`:78-79`). The hull's satisfaction
is at the STAGE carrier: `T`'s `_⊨₀_` reads at `AbsL.𝒮M` for
`AbsL = Single 𝒮ᵥ (λ x → x ∈ˢ Lset α) Ltr` (`src/L/Hull.lagda.md:153`,
`:323`). The two carriers are different types, and `IsOrd` does not join them.

`[LJ-1.642]` measured this ONE TASK BEFORE this brief was written, and named it
wall 1:

> Without a Levy certificate the stage-to-class transfer (`σ₁-up`,
> `src/FOL/Absoluteness.lagda.md:182-184`) does not apply, so no reading of a
> stage satisfaction reaches `Lset-only` (`src/L/Hierarchy.lagda.md:334`),
> which is the only determination the tree proves.

Basis: `agents/tasks/LJ-1-642/lj-1.642-report.md:190-195`.

## THE VEHICLE THE BRIEF NAMES IS THE WRONG GRADE

`feed` puts `absFo LsetGraph` under `wit` (`agents/tasks/LJ-1-474/Probe474.agda:131`).
`FOL.Absoluteness` delivers exactly three transfers, and each one asks for a
Levy certificate: `abs₀` for `Δ₀` (`src/FOL/Absoluteness.lagda.md:122`),
`σ₁-up` for `Σ₁` (`:182`), `π₁-down` for `Π₁` (`:187`).

`LsetGraph` carries NO Levy certificate:

- `grep -rnE '(Δ₀|Σ₁|Π₁)-(LsetGraph|GraphAt|StepAt|ApproxAt|DefAt|StepBody)' src/`
  returns 0 lines.
- The tokens `Δ₀` and `Σ₁` occur ZERO times in each of
  `src/L/Coding/Sequence.lagda.md`, `src/L/Hierarchy.lagda.md` and
  `src/L/Coding/Powerset.lagda.md`.

So no transfer applies to the packaged graph in either direction, and no added
hypothesis on the argument slot repairs that.

## THE GRADE MATCHES DEVLIN'S OWN REQUIREMENT LIST

`dev/literature/devlin-II5.md:224-227` states requirement 3:

> 3. Σ₀ absoluteness for the matrix: 1.9.15 moves L_α's (or M's) satisfaction

The route needs a Σ₀ MATRIX. The tree has one, and it is not `LsetGraph`. It is
`levelHoodB`, with its certificate beside it:

    levelHoodB : Formula CS.S (suc (suc (suc (suc n))))
    Δ₀-levelHoodB : Δ₀ levelHoodB

Basis: `src/L/BoundedSubset.lagda.md:108`, `:113`.

## WHAT THE TREE LACKS, IN THREE PIECES

1. **A READING of the Σ₀ matrix.** `levelHoodB` is syntax only. `levelHood`
   occurs in `src/` at TWELVE lines, ALL of them inside
   `src/L/BoundedSubset.lagda.md` (`:108`, `:109`, `:113`, `:114`, `:142`,
   `:143`, `:145`, `:146`, `:849`, `:852`, `:856`, `:868`), and every one of
   them is a definition or a Levy certificate. No lemma turns a satisfaction of
   it into
   `v ≡ Lset γ`. The chapter says so itself: "the level-hood instantiation at
   the hull is the priced residue" (`src/L/BoundedSubset.lagda.md:901-902`).
2. **AN AGREEMENT between the bounded rows and the machine rows.** The bounded
   graph is `GraphB.graphBndAt` (`src/L/Condensation.lagda.md:2492-2493`) with
   `Δ₀-graphBndAt` (`:2495`). The delivered agreement arrows are FOUR, and all
   four are leaf rows: `extAtB→extAt` (`:2514`), `extAt→extAtB` (`:2524`),
   `emptyB→emptyAt` (`:2724`), `emptyAt→emptyB` (`:2729`). Nothing lifts the
   agreement to `approxBndAt`, `stepBndAt` or `graphBndAt`.
3. **DEVLIN 2.6(ii), the witness inside the carrier.**
   `dev/literature/devlin-II5.md:220-222` asks for it: "The forward half needs
   the witnessing z to live inside L_α; that is 2.6(ii), the sequence
   (L_δ | δ ≤ γ) ∈ L_α for γ < α". `hierL` is built by
   replacement in `L` (`src/L/Hierarchy.lagda.md:621-622`) and carries no level
   bound. This is `[LJ-1.642]`'s wall 4 and it is the mathematics, not the
   syntax.

## WHAT IS DELIVERED HERE INSTEAD

`Probe646.agda` typechecks. It carries:

- `code-ord-mem`: an ordinal code's value is a member of `lam`, not only of
  `Lset lam`. This closes the gap `[LJ-1.479]` stopped at
  (`agents/tasks/LJ-1-479/lj-1.479-report.md:84-88`), in one line, from
  `ord∈Lset→∈` (`src/L/Ordinal/Stages.lagda.md:265-268`).
- `Wit.wit-sat`: the value of a `wit` code satisfies the code's own formula, as
  soon as the stage has any witness. Generic in the formula.
- `join`: the obligation follows from exactly TWO residues, `StageSat` and
  `ReadOff`, and the reduction typechecks.

`StageSat` is Devlin 2.6(ii) at the packaged graph. `ReadOff` is `Lset-only` at
the stage carrier. Neither is deliverable today, for the reasons above.

## WHAT WOULD CHANGE THE VERDICT

A brief that funds the READING of `levelHoodB` at two slots, and its
instantiation at the hull's code alphabet. `join` in this probe is generic in
nothing: it is stated at the predecessor's `feed`. A `join` at a Σ₀ matrix would
be the same three lines, and then only Devlin 2.6(ii) is left.
