# Review of `kappa-coded`

The obligation is a hole. This file is the obstruction, for the branch
`no-go-stated`.

## THE STATEMENT

```
kappa-coded : ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a κ ∥₁
```

It is `Probe426.agda:135-136`. Generic in `a`, with ordinal certificate
`oa` as a module parameter (`Probe426.agda:110`). `SiteBound a` and
`LeastCardInjL a oa` are in scope (`:112-113`). No cardinal, no site, no
numeral. Agda reports `UnsolvedInteractionMetas` at
`Probe426.agda:136` (`runs/kappa-coded-hole-1.out:2-4`).

## D-10

The ambient injection exists, truncated (`src/L/Cardinal.lagda.md:133`).
What is missing is a constructible set that codes it. See
`lj-1.426-report.md` section D-10. The type is not proved and not
refuted.

## HALF B IS NOT THE BLOCK

`from-graph` is GREEN (`Probe426.agda:129-130`, `runs/w3-1.out`, exit 0,
median 1.71 s over three forced rechecks). Given `G` and the four
membership readings, `code-from-graph` at `x := a` and `d := κ` returns
`InjCode G a κ`. The remaining bill is HALF A at this pair.

## HALF A AT THIS PAIR, THE BLOCK

HALF A at a generic pair is the type `HalfA` at
`agents/tasks/LJ-1-414/Probe414.agda:65-66`. This task asked it at one
named pair, `a` and its own least cardinal `κ`.

The four candidate suppliers are answered in `lj-1.426-report.md`
section 2. None of them produces a graph of `κ-inj` at this pair.

- `OrdIncl` gives the inclusion of `κ` into `sucV (fst a)`, which is the
  wrong direction (`src/L/InjChain.lagda.md:604-608`; membership
  `src/L/Cardinal.lagda.md:129-130`). The needed direction does not even
  instantiate: `⟨ fst a ∈ fst κ ⟩` is false by `idInj` and `κ-min-at`.
- `Comp` chains coded graphs it is given
  (`src/L/InjChain.lagda.md:314-324`). It does not manufacture a first
  factor.
- `sep` takes a `Formula S 1` (`src/L/Absorption.lagda.md:400-401`). A
  truncated ambient function is not a formula
  (`src/FOL/Syntax.lagda.md:94-100`; `src/L/Cardinal.lagda.md:133`).
- Minimality, membership in `sucV (fst a)`, and the `leastOf` selection
  do not give a graph (`src/L/Cardinal.lagda.md:140-141`, `:129-130`,
  `:116-117`).

## WHAT WAS NOT DONE

No axiom, no postulate, no module parameter that asserts HALF A. HALF A
itself was not attempted. Audit finding F6 records that the one attempt
to join the halves was killed at 8.5 GB RSS
(`dev/pod/audit-2026-08-20.md:88`). The obligation stays a hole.

This is not a refutation of the type. The `[LJ-1.414]` report returned
NO-GO on the general implication and did not refute it
(`agents/tasks/LJ-1-414/lj-1.414-report.md:39`). This return names the
same missing link at one named ordinal.

## C-42

No refutation landed, so C-42's sweep of a false shape does not apply.
The named missing link is HALF A at `(a, κ)`.
