# review-of-approx-in-stage

**NO-GO on `approx-in-stage` as the brief spells it. The obligation is not
built and no postulate stands in for it.** The probe is GREEN
(`agents/tasks/LJ-1-517/runs/full-1.out`, exit 0). The witness meter reads
`1 UNRESOLVED of 1, probe_red=False`
(`agents/tasks/LJ-1-517/runs/witness.out:2`).

This file is the critic's input. It does not close the task.

## 1. WHAT THE BRIEF ASKED, AND WHAT THE ANSWER IS

The brief asked for a witness for `ApproxAt` that lies in the stage and that
is NOT `hierL`. **The answer has two halves and they point in opposite
directions.**

**HALF ONE. `hierL` is NOT the only approximation the tree builds, so the
census does not close the door by itself.** `approxSet`
(`src/L/Choice/Before.lagda.md:1035`) is a second one, and it IS placed in a
stage. Census row 4 and row 5 of the probe typecheck against the delivered
names (`agents/tasks/LJ-1-517/Probe517.agda:98`, `:106`).

**HALF TWO. THE WITNESS SLOT IS ALREADY GENERIC, AND THE OBLIGATION STILL
DOES NOT FORM A TERM.** `graph-table` takes the approximation as a parameter
(`src/L/Hierarchy.lagda.md:382`); census row 2 typechecks that genericity
(`agents/tasks/LJ-1-517/Probe517.agda:74`). The obstruction is therefore NOT
the choice of witness. It is a price that EVERY witness pays.

## 2. THE PRICE, MACHINE CHECKED

`witness-forces-levelIn` (`agents/tasks/LJ-1-517/Probe517.agda:181`) is a
term. It says:

> if `f` approximates the tower below `δ` and `f` lies in `Lset α`, then
> `Lset c` lies in `Lset α` for every `c` in `δ`.

That conclusion is `levelIn` below `δ`. **`levelIn` is a HYPOTHESIS at every
site in the live tree**: `src/L/BoundedSubset.lagda.md:917` and
`src/L/BoundedSubset.lagda.md:1555` both take it as a module parameter. So
the obligation is at least as strong as a statement the tree assumes.

`obligation-gives-levelIn` (`agents/tasks/LJ-1-517/Probe517.agda:191`) states
the same fact against the brief's own type, so no inhabitant escapes it.

**AND THE PRICE IS HIGHER THAN `levelIn`.**
`witness-forces-two-below` (`agents/tasks/LJ-1-517/Probe517.agda:204`) is a
term too. It says the witness needs `Lset c` in `Lset γ` for some `γ` in
some `β` in `α`. **The witness does not want room in `Lset α`. It wants room
two membership steps below `α`.**

## 3. WHY THIS IS A STOP AND NOT A GUESS

The brief forbids a postulate and forbids a reflection hypothesis. The two
terms above show what would have to be supplied, and the tree supplies
neither. A term written today would have to assume `levelIn`, which is the
same debt `[LJ-1.492]` and `[LJ-1.494]` recorded.

I did not build a term of the negation. This is an obstruction, not a
refutation of the type.

## 4. WHAT THE BRIEF GOT WRONG, AND IT IS FIXABLE

**The brief asked for the wrong thing. The orthodox statement is not "a
different witness". It is "the same witness, under a limit hypothesis on
`α`".** Devlin 2.6(ii) states the sequence `(L_δ | δ ≤ γ)` is in `L_α` for
`γ < α`, **at limit `α > ω`** (`dev/literature/devlin-II5.md:218`,
`dev/literature/devlin-II5.md:221`). The witness in that argument IS the
level sequence, which is `hierL`.

`witness-forces-two-below` and that hypothesis agree exactly: two membership
steps of headroom inside `α` is what a limit `α` always has, and what an
arbitrary `α` does not.

**So the door `[LJ-1.494]` left open leads back to `hier-in-stage`, and the
missing piece is a hypothesis on `α`, not a second witness.**
