# review of `defines-level-across`: the obligation is NOT inhabited

## VERDICT

**`BChain.DefinesLevelAcross`, clause (iii), IS NOT SUPPLIED, AND I DID NOT
INHABIT IT.** The meter says so:
`agents/tasks/LJ-1-602/Probe602.agda::defines-level-across` returns
`missing exit=42 ... [NotInScope]`, `1 UNRESOLVED of 1`, `probe_red=False`
(witness run, 2.50 s). The probe itself is green
(`agents/tasks/LJ-1-602/runs/p-5-forced.out`, `EXIT=0`, forced recheck,
11.82 s).

**AND THE STOP IS NOT ABOUT FORMULAS AT ALL. IT IS AN EQUIVALENCE, AND BOTH
DIRECTIONS ARE LANDED TERMS.** Clause (iii)
(`agents/tasks/LJ-1-578/Probe578.agda:503-510`) is the CONDENSATION COMMUTE
dressed in syntax:

- **Any inhabitant of clause (iii) IS the commute**
  (`across-gives-commute`, `agents/tasks/LJ-1-602/Probe602.agda:189-197`):
  the image `g (Lset δ , Lδ∈M)` satisfies the mapped formula by the
  delivered transfer `iso-inv` (`src/L/BoundedSubset.lagda.md:195`), so the
  clause's uniqueness conjunct applied at that image concludes
  `HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)`. This is `[LJ-1.578]`'s own
  `b-from-across` (`Probe578.agda:513-514`) with its Fact A supplied by the
  clause's own hypothesis `Lδ∈M` instead.
- **The commute GIVES clause (iii)** (`commute-gives-across`,
  `Probe602.agda:212-219`): at the EQUATION formula
  `var zero ≐ con (Lset δ , Lδ∈M)` (`eqA`, `:200-201`), satisfaction is
  `refl` (`eq-sat`, `:203-205`) and uniqueness is path equality read at the
  restricted structure (`eq-uniq`, `:207-210`; the `[LJ-1.598]` equation
  mechanics, `src/FOL/ZFStructure.lagda.md:148` on `:82`,
  `src/FOL/Semantics.lagda.md:93`). **No graph formula, no determination, no
  witness selection is owed on this clause.**

**SO THE WHOLE PRICE OF CLAUSE (iii) IS ONE SET-LEVEL STATEMENT**,
`Commute` (`Probe602.agda:178-181`), `[LJ-1.578]`'s `Facts.LevelsCommute`
(`Probe578.agda:126-128`) at the clause's own hypotheses. It is not built:

- `[LJ-1.477]` attacked the MORE GENERAL type `PiCommuteLset`
  (`agents/tasks/LJ-1-477/Probe477.agda:100-102`, no `IsOrd (π y)`, no
  `Lset y ∈ M`) and stopped at the join of the two computation laws
  (`lj-1.477-report.md`, VERDICT: "NO-GO at the join"), naming as candidate
  obstruction a NON-ORDINAL collapse. Clause (iii)'s hypothesis
  `IsOrd (HS.C.π δ)` excludes exactly that case, so the clause stands or
  falls with the commute AT ORDINAL COLLAPSE, which nobody has built
  (`grep -rn "LevelsCommute" src/` returns nothing).
- `[LJ-1.489]` is NO-GO on the sibling commute with the definable powerset
  (`review-of-piCommuteD.md`), same wall family.

## WHAT I DELIVERED INSTEAD, AND WHAT EACH ONE COSTS THE NEXT BRIEF

Every row typechecks; the fourteen names were metered and return
`0 UNRESOLVED of 1` each, `probe_red=False` (2.61 s to 2.75 s per run).

| term | `Probe602.agda` | what it settles |
|---|---|---|
| `Frame.OnlyAcross` | `:112` | W3: clause (iii)'s collapse reading, alone, TYPE ONLY |
| `Frame.only-across-vacuous` | `:120` | the conjunct ALONE is vacuously inhabited; the weight is the conjunction |
| `Frame.DefinesLevelAcross` | `:133` | clause (iii), restated text for text from `Probe578.agda:503-510` |
| `Frame.clause-iii-from-body` | `:150` | the body identity: `Body` is clause (iii) per code |
| `Frame.Commute` | `:178` | the residue, named: the commute at the clause's hypotheses |
| `Frame.across-gives-commute` | `:189` | clause (iii) IMPLIES the commute, no Fact A needed |
| `Frame.eqA`, `eq-sat`, `eq-uniq` | `:200`, `:203`, `:207` | the equation route at the collapse, both halves free |
| `Frame.commute-gives-across` | `:212` | the commute GIVES clause (iii), outright |
| `Frame.iso-inv-at-the-site` | `:237` | the forward transfer, at one free variable, this site |
| `Frame.collapse-satisfiers-lift` | `:247` | every collapse satisfier IS the image of a hull satisfier |
| `Frame.image-trans` | `:264` | the collapse's carrier is transitive; the hull's is not delivered so |

## THE ONE THING THE NEXT BRIEF SHOULD DECIDE

**Clause (iii) should be replaced by the commute itself, exactly as
`[LJ-1.595]` proposed replacing clause (ii) by the truncated `Facts.Covered`
(`review-of-defines-cover.md`, "THE TWO THINGS", item 1).** The clause buys
no formula-side content beyond `Commute` (section 3 of the probe is the
whole distance), and `Commute` is the statement every route already prices:
`[LJ-1.477]`'s computation-law join, `[LJ-1.160]`'s `crossOut` at the
transitive image (`agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71-72`), and
`[LJ-1.578]`'s own `Facts.LevelsCommute`. Whether one supplier can pay the
commute and clauses (i)/(ii)'s residues together is the mathematician's
call; this file does not price it.

## SCOPE

I wrote only inside `agents/tasks/LJ-1-602/`. Nothing is postulated, the
probe carries `--safe`, there is no hole, and nothing lands in `src/`.
No commit, no push.
