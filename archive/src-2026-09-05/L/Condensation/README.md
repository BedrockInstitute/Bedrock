# Condensation

The twelve-row agreement, split across separate masters so no single Agda
process elaborates all twelve rows.

`LowerAgree.lagda.md` proves the first six rows (membership, equality,
conjunction, disjunction, implication, negation) at an abstract
environment. `UpperAgree.lagda.md` proves the last six rows (top, bottom,
existential, universal, all-in, exists-in). Each carries only the site
facts its rows use.

`TwelveAgree.lagda.md` is the composer. It applies the two partials'
already-proved `out`/`back` at the full sixty-nine-fact frame and conjoins
them into the twelve-row agreement in both directions. It does not re-apply
the rows.

The masters import the row agreements from `src/L/Condensation.lagda.md`.
The old `TwelveAgree` submodule in that master was vacuous
([LJ-1.71], machine-checked) and was removed ([LJ-1.76]).
