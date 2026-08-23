# review of `inner-to-ambient`: the outright commute is NOT inhabited; the term names precisely what it lacks

## VERDICT

**THE OUTRIGHT COMMUTE IS NOT SUPPLIED, AND I DID NOT INHABIT IT.**
`Commute` (`agents/tasks/LJ-1-606/Probe606.agda:127-130`, `[LJ-1.602]`'s
`Probe602.agda:178-181` letter for letter) is OPEN at this frame. What the
brief's obligation sentence sanctions is delivered instead: ONE green term
whose TYPE names the three missing faces,

    inner-to-ambient
      : (the six hull slots)
      → ElemDownAt        -- FACE E
      → Crossing          -- the graph matrix with FACE G+ and FACE G-
      → Commute

at `agents/tasks/LJ-1-606/Probe606.agda:303-313`, metered
`pass exit=0`, `0 UNRESOLVED of 1`, `probe_red=False` (3.14 s), forced
recheck green (`runs/p-10-final.out`, 4.77 s, peak 726,712,320 bytes).

**THIS IS NOT A FOURTH CLAUSE ATTEMPT AND NOT A RESTATEMENT OF
`[LJ-1.578]`'s `b-from-across`.** That term said "clause (iii) plus Fact A
gives the commute". This term says what the COMMUTE itself is made of, and
the answer is sharper than the certificate's own currency expected: the
commute is ONE TRANSFER of the level-graph statement, needing NO induction
on the tower, NO Fact A below `δ`, and NO def-hood lifting
(`Probe606.agda:206-247`, the five legs). Everything between the faces and
the conclusion is DELIVERED machinery: the collapse iso
(`src/L/BoundedSubset.lagda.md:195`, `:250`, instantiated at `:321`) and
the Sigma-one lift at the transitive image
(`src/FOL/Absoluteness.lagda.md:182-185`, which `[LJ-1.160]` measured opens
at `πX` in one line, `agents/tasks/LJ-1-160/ProbeLJ1160A.agda:49-53`).

## THE THREE FACES, WITH STATUS

| face | statement | at `file:line` | status |
|---|---|---|---|
| E | elementarity down at the hull, all arities | `Probe606.agda:147-149` = `DownReflect.ElemDown`, `src/L/BoundedSubset.lagda.md:410` | UNBUILT at the six slots; DELIVERED at `[LJ-1.570]`'s seventeen (`agents/tasks/LJ-1-578/Probe578.agda:413-427`, `elem-down-taken`) |
| G+ | the stage carries the graph at the tower's own values | `Probe606.agda:156-159` | UNBUILT; the witness-in-carrier half of Devlin 5.2's (b); the `Adeq` shape of `[LJ-1.570]` (`agents/tasks/LJ-1-570/Probe570.agda:319-322`) |
| G- | the ambient graph statement at an ORDINAL index pins the level | `Probe606.agda:168-172` | UNBUILT; Devlin 5.2's (a); `[LJ-1.160]`'s `crossOut` made concrete (`agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71-72`) |

**THE KIT CANNOT BE FILLED WITH JUNK, BOTH WAYS, AS TERMS**
(`Probe606.agda:260-285`): a TRUE matrix fails G- outright
(`⊤-fails-G-`, `:262`), a FALSE matrix fails G+ at any genuine level-pair
(`⊥-fails-G+`, `:275`). So `Crossing` is inhabited exactly when the
level-graph adequacy holds at this site: G+ and G- ARE clause (i)'s own
residue, which `[LJ-1.598]` priced NO-GO on the formula side
(`agents/tasks/LJ-1-598/lj-1.598-report.md`, VERDICT).

**WHERE THE CLAUSE'S OWN HYPOTHESES ARE SPENT.** `IsOrd (HS.C.π δ)` is
spent at G- ALONE (the ambient decode is gated at the ordinal index);
`Lδ∈M` puts the level pair inside the hull so FACE E can move it. The
index-generality of G+ is a measured gap: the tree's graph formula is
ordinal-indexed and answers with a NON-level at a non-ordinal index
(`[LJ-1.598]`, the `δ = {{∅}}` reading), while `Commute`'s telescope does
not hypothesize `IsOrd δ`. A supplier has two roads: rebuild the graph
all-index (the ∈-recursive reading), or weaken clause (iii)'s currency by
`IsOrd δ`. That choice is the mathematician's; this file does not make it.

## WHAT THIS PRICES FOR ROW 3

**THE THREE CLAUSES SIT ABOVE ONE OBJECT, AND IT IS NOT A CLAUSE.** With
`[LJ-1.602]`'s equivalence (clause (iii) ⟺ commute) and this term
(commute ⟸ graph adequacy + elementarity), row 3's whole price is:
the level-graph adequacy (G+ and G-, clause (i)'s residue) plus the
elementarity face E (delivered one frame wider). Clause (ii) does not
enter: `[LJ-1.595]` already truncated it away
(`agents/tasks/LJ-1-595/review-of-defines-cover.md:3-5`). A fourth clause
attempt would price the same object a fourth time.

## SCOPE

I wrote only inside `agents/tasks/LJ-1-606/`. Nothing is postulated, the
probe carries `--safe`, the delivered file has no hole, and nothing lands
in `src/`. No commit, no push.
