# [LJ-1.629] stop: the bill's site is NOT an initial ordinal; conjunct 2 is FALSE at a site the bill admits

## THE STOP

**NO-GO, stated, on `site-is-init : SiteIsInit`.** The type is the
brief's obligation verbatim, `agents/tasks/LJ-1-629/Probe629.agda:81-85`:
the bill's three site hypotheses (`IsOrd (fst κ)`, `IsCardinalL κ`,
`⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥`, `[LJ-1.589]`'s spelling at
`agents/tasks/LJ-1-589/Probe589.agda:245-247`) implying `Init (fst κ)`
(`src/L/Ordinal/SquareLaw.lagda.md:692-698`). No term of the probe
carries the obligation's name and no term has its type. The probe is
GREEN (`runs/final-12.out`, 2.76 s, exit 0), carries no hole and no
postulate, and its rows are the measurement. Nothing landed in `src/`.
Nothing was committed and nothing was pushed.

The target is not merely unprovable: **it is refutable modulo one true
fact.** `target-false : IsCardinalL ωʟ → SiteIsInit → Empty.⊥`
(`agents/tasks/LJ-1-629/Probe629.agda:135-137`) is green. The two
hypotheses of the bill that hold at `κ := ωʟ` are green terms
(`ord-ωʟ`, `∉-ωʟ`, `:124-128`); the third, `IsCardinalL ωʟ`, is TRUE
(a code at a member `δ ∈ ω` reads back to an ambient injection
`⟪ω⟫ ↪ ⟪δ⟫` with `δ ≡ # n`, and the tree's own pigeonhole
`no-inj-finite`, `src/L/Ordinal/SquareLaw.lagda.md:604-660`, refutes
exactly that shape) and is priced, not built, in the report.

## THE FOUR CONJUNCTS (the deliverable)

| conjunct | verdict | evidence |
|---|---|---|
| 1 `IsOrd (fst κ)` | GIVEN, verbatim, the bill's first hypothesis | `c1-given`, `Probe629.agda:106-109` |
| 2 `⟨ ω ∈ˢ fst κ ⟩` | MISSING, and FALSE at a site the bill admits | `init-ω-false`, `Probe629.agda:121-122`; `target-false`, `:135-137` |
| 3 successor closure | PAYABLE from the bill GIVEN conjunct 2 | `c3-payable`, `Probe629.agda:224-230` |
| 4 the ambient non-injection | MISSING at the stated grain; needs ambient cardinality AT THE SITE plus a pairing at every infinite member of the site | `c4-from`, `Probe629.agda:252-266` |

**Conjunct 2 is the falsifier.** The trophy clause excludes
`fst κ ∈ˢ ω`; it does NOT exclude `fst κ ≡ ω`. At `κ := ωʟ`
(`fst ωʟ` is `ω` by definition, `src/L/Axioms/Infinity.lagda.md:69-70`)
conjunct 2 demands `⟨ ω ∈ˢ ω ⟩`, which `∈-irrefl` refutes
(`src/V/Hierarchy.lagda.md:155`). `[LJ-1.116]` measured the same fact
at the demand side (`archive/dev/LJ-dispatch-index.md:192`, "Init is
false at omega and at successors"); this task re-measures it AT THE
BILL'S SITE, and the bill admits the site.

**Conjunct 3 is honest work, not a wall.** Given `⟨ ω ∈ˢ fst κ ⟩`,
closure is green: numerals close inside `ω` inside the site
(transitivity), and an infinite member can close only through the
middle trichotomy case `sucV γ ≡ fst κ`, where `IsCardinalL` refutes
the coded successor shift the tree already carries (`shift-coded`,
`src/L/CodedShift.lagda.md:37-41`).

**Conjunct 4 is the real demand, and it is ambient.** The brief's
reading is CONFIRMED: `IsCardinalL` refutes CODED injections only
(`src/L/Cardinal.lagda.md:238-241`); conjunct 4 asks that NO AMBIENT
injection send `⟪ fst κ ⟫` into the square of an infinite member.
The green row `c4-from` measures exactly what closes it: ambient
`IsCardinal` AT THE SITE (`src/L/BoundedSubset.lagda.md:1046-1047`)
plus a pairing at EVERY infinite member of the site.

## IS (iii) ROW 1: NO

Row 1 (`AmbientCardAtSucc`, `agents/tasks/LJ-1-550/Probe550.agda:301-302`)
asks ambient cardinality AT THE SUCCESSOR `δ` of each internal
cardinal, which is where the bridge spends it
(`member-in-stage` consumes `r1` as `IsCardinal (fst δ)`,
`agents/tasks/LJ-1-550/Probe550.agda:257-259`, applied at `:355`). Conjunct 4 needs
ambient cardinality AT THE SITE `κ` ITSELF, an instance row 1 never
covers at `ω` or at any limit cardinal above it (nobody's successor),
PLUS the band pairing below the site. The green rows
`ambient-all→row1` (`Probe629.agda:282-284`) and `route`
(`:289-294`) measure both directions of the comparison: row 1 is a
proper weaken of ambient cardinality at every internal cardinal, and
the Init route's payoff (`via-col-square` at the site) is real exactly
if a premise holds that the bill does not give. **The campaign does
not hold one row where it thought it held two; the Init route, where
it could run, would cost MORE than rows 1 and 2 together.**

## WHAT WOULD REOPEN IT

- Respelling the trophy clause to its strictly-above-`ω` form,
  `⟨ ω ∈ˢ fst κ ⟩` replacing `⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥`, removes the
  falsifying site. Even then conjunct 4 stands: ambient cardinality at
  every site cardinal plus the band below every site. That is a bill
  change, not a proof, and it is the mathematician's to make.
- Ambient cardinality at every internal cardinal, plus the band, pays
  `Init` at every site and with it `sq` at every site: strictly more
  than rows 1 and 2 together. No axiom is needed on this route and
  none was used.

## WHAT THIS TASK DID NOT DO

No axiom was added and none was postulated; the owner's ruling that
the axiom surface is closed was not touched. `via-col-square` was
consumed, not rebuilt (`route`). Nothing landed in `src/`. Nothing was
committed and nothing was pushed.
