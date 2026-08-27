# Review of `bound2-in-limit`: NOT INHABITED

**Verdict: NO-GO.** The obligation
`agents/tasks/LJ-1-710/Probe710.agda::the-obligation` (the brief's
`bound2-in-limit`) is not inhabited by this dispatch. The statement is not
shown false. This file states the stop; the green frame and the merge at an
own-name presentation live in the same probe, both typechecking
(`agents/tasks/LJ-1-710/runs/final.out`, EXIT=0).

## What was asked and what closed

The brief names one term: a limit that contains `σ₁` and `σ₂` contains
`fst (bound2 σ₁ σ₂ o₁ o₂)` (`bound2` at `src/L/Ordinal.lagda.md:185`). The
design that the two recorded predecessor conversions pointed to was built,
green, under the trimmed frame:

- A presentation-honest limit predicate carrying ordinality, successor
  closure and small-family union closure
  (`agents/tasks/LJ-1-710/Probe710.agda`, Section 1). Cold floor 1.37 s,
  278 MB (`runs/t-small.out`), against a 28.12 s cone-loaded predecessor
  floor.
- At that limit, the full merge statement CLOSES for a family written out
  loud in this file: `bound2OwnLimit`, two clause compositions, plus its
  ordinality free from `suc-ord`/`setUnion-ord`
  (`agents/tasks/LJ-1-710/Probe710.agda`, Section 3).
- So every mathematical ingredient around the unpaid lemma is in hand. Only
  the NAME PARITY between `succFam σ₁ σ₂` and bound2's internal family is
  missing, and it is unobtainable from inside a probe.

## The measured wall, twice restructured

1. Elaboration-time unification, not `refl`: instancing the union closure
   clause at my written family against the goal set fails with
   `[UnequalTerms]`, `L.Ordinal.f σ₁ σ₂ o₁ o₂ x != mf x`
   (`runs/t-e1.out:5-9`). This is not the predecessor's p-26 measurement
   repeated: no equation was asserted; the checker itself unified the
   families and refused them at the variable position.
2. Name reference: Agda prints bound2's where-bound family as
   `L.Ordinal.f σ₁ σ₂ o₁ o₂`, but the symbol is outside scope:
   `L.Ordinal.bound2.f` is `[NotInScope]` (`runs/t-paths2.out:5-8`).
3. General conversion fact discovered on the way: even a locally defined
   clause function is NOT convertible to its own written-out case lambda at
   a variable position, `mf x != (λ { (lift true) → ... ; (lift false) →
   ... }) x` (`runs/t-selflambda.out:5-6`). No family-equivalence proof in
   this development style can pass through a function-vs-case-tree
   comparison without first splitting on the index.

With one clause-lambda index split, leaf positions normalize (that is how
Section 3 closes); but `eqImage mf internalFam` cannot even be STATED,
because the second argument has no name.

## D-10: the target's truth

Not shown false. Classically the merge ordinal of two members below a limit
ordinal lies below it again (it is the successor of the larger member), and
every classic reference this task cites treats the merge as interior to any
limit; the obstruction measured here is a NAMING obstruction of the source
tree, not a Tarskian or cardinality obstruction of the statement.

## What would reopen the route (minimal cure, src side)

One line of new public surface in `src/L/Ordinal.lagda.md`, either:

- name the binary merge family as a top-level definition and build `bound2`
  from it (then probes cite the same symbol on both sides), or
- prove the membership lemma directly in `src/`: from `IsOrd α`,
  `⟨ σᵢ ∈ₛ α ⟩` conclude `⟨ fst (bound2 σ₁ σ₂ o₁ o₂) ∈ₛ α ⟩` under a
  union-closed notion of limit; the probe's Section 3 body is the whole
  proof skeleton, needing only the successor of each member supplied by the
  limit's own successor clause.

Until then, `[LJ-1.705]`'s split plan stands with its second half payable
only after that surface exists. Nothing in `src/` changed in this dispatch;
the working tree carries only `agents/tasks/LJ-1-710/`.
