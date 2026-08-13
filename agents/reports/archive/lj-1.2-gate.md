# LJ-1.2 gate: can the level story be certified Delta-0 clause by clause at the class carrier?

Status: COMPLETE. Probe file: `src/ProbeLJ12.lagda.md`, untracked, never
committed. Report written incrementally.

## 1. VERDICT

**NO-GO.** The step clause resists bounding without a new carrier fact.

The three criteria, stated as pass or fail each:

1. Criterion 1 (every clause certifies at 25 non-blank in-fence lines or
   fewer): FAIL. The approximation clause certifies. The step clause does
   not certify at all. Its Delta-0 witness does not exist.
2. Criterion 2 (the Sigma-1 witness assembles): FAIL. The witness needs the
   core Delta-0. The core contains the step clause. The step clause is not
   Delta-0.
3. Criterion 3 (the equivalence closes at 350 non-blank in-fence lines or
   fewer): NOT REACHED. The equivalence reconciles the certified story with
   the delivered description. The certified story does not exist.

## 2. THE MEASUREMENT

The probe is 122 non-blank in-fence lines. One Agda process at
`GHCRTS=-M8g`. Wall 2.5 to 2.7 seconds per check, warm dependencies. The
certified portion exits 0. The step-clause witness check exits 42.

The per-clause table:

| clause | bounded rewrite | Delta-0 witness | non-blank lines | verdict |
|---|---|---|---|---|
| domain clause of the approximation | written, pair-bounded | closes | 10 | PASS |
| step-condition frame of the approximation | written, pair-bounded | closes, parameterized by the step clause | 11 | PASS |
| approximation assembly | written | closes | 4 | PASS |
| step clause, with its DefAt and satisfaction leaves | written | does not close | 23 for the formula alone | FAIL |

The step-clause witness check fails with this Agda error, exit 42:

```
∃̇∈ _t_460 _φ_461 !=
∃̇
(∃̇
 (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc (suc zero))))) ∧̇
  appAt (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero))
  zero
  ∧̇ stepLeaf))
of type Formula S 7
when checking that the inferred type of an application
  Δ₀ (∃̇∈ _t_460 _φ_461)
matches the expected type
  Δ₀
  (∃̇
   (∃̇
    (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc (suc zero))))) ∧̇
     appAt (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero))
     zero
     ∧̇ stepLeaf)))
```

The Delta-0 data has no constructor for the unbounded existential
(`src/FOL/LevyHierarchy.lagda.md:47-57`). The only existential constructor
is `δ-∃∈`, and it demands a bound term. No bound term exists for the code
or for the table value.

The expected cost was 250 to 400 non-blank lines and 2 to 15 seconds. The
probe is 122 lines and 2.5 to 2.7 seconds. The miss is a measurement: the
top-level clause rewrites are cheap, and the cost is entirely the missing
bounds, not the line count.

## 3. CARRIER-GENERIC OR NOT (DD4)

The approximation clause's rewrite is parameter-free. Its bounds are
variables. It works at any carrier.

The step clause's obstruction is not about the class carrier. The delivered
satisfaction leaves carry unbounded quantifiers at every carrier. The code
set is a level member at the class carrier, and that is not enough. The
missing fact is a bounded object-level description of the code set and of
the table. That content is generic. P-l does not rescue the certification:
the blocker is the leaves' quantifier structure, not the carrier's
presentation.

The certification is not carrier-generic as a whole. It fails at every
carrier until the bounded satisfaction substrate exists.

The cost of making it generic is zero beyond the substrate. The rewrite
is already parameter-free. The substrate is the missing content. It is
the bounded object-level description of the code set and of the table.
It is priced in section 5.

## 4. WHAT THE CROSSING NOW PRICES AT

The crossing re-prices at about 5.0 to 5.1 thousand lines. This is the D32
Build A band. `[LJ-1.5]` is not funded at the survey band. The plan stops
for a re-price (DD8). The wing is projected at 8.0 to 10.8 thousand lines
total. This one term moves the phase by about half its size.

## 5. IF NO-GO: WHICH CLAUSE, WHICH FACT, WHAT NEXT

The step clause resisted. Its DefAt and satisfaction leaves wanted two
bounds. Both are missing.

Fact 1: the code existential. The natural bound is the code set over the
carrier. The tree delivers the code set as a sealed meta-level element,
`Codes` and `AllCodes` (`src/L/Coding/CodeSet.lagda.md:468-469`,
`:555-556`). It also delivers the object-level formula `CodesAt`
(`src/L/Choice/Faithful.lagda.md:334-335`). `CodesAt` is not Delta-0. Its
`isCodeAnyAt` carries `hasWitnessAt`'s unbounded existential over the
witness set (`src/L/Choice/Faithful.lagda.md:287-288`,
`src/L/Coding/CodeSet.lagda.md:250-251`). No bounded object-level
description of the code set exists.

Fact 2: the table-value existential and the twelve-clause table. The value
is the satisfaction table's entry at the code. The tree delivers
`satTable` as a meta-level element of the model, not as an object-level
formula (`src/L/Coding/Table.lagda.md:103-104`). The delivered graph binds
the index set, the table, and the carrier with three unbounded
existentials (`src/L/Coding/Graph.lagda.md:104-112`). The twelve clauses
carry unbounded quantifiers as delivered. `atomRel` has an unbounded
universal (`src/L/Coding/Model.lagda.md:1766-1769`). `propRel` has two
(`:1073-1077`). `extAt` has two (`:662-664`).

The next candidate technique: build the bounded satisfaction substrate
first. It is a bounded object-level description of the code set and of the
twelve-clause table at a carrier. This is the archived crossing-rebuild
content. Its measured price is 5,047 lines (T257 section 4.2). The
alternative is the cone abstraction fork at 1.0 to 1.7 thousand lines
(T51 section 5).

## 6. ARCHIVE USED

- `archive/rud-route/src/L/Condensation.lagda.md:565-603`: the archived
  level story, Delta-0 certified, Def-step entry collapsed to `⊤̇`. Its
  clauses are the structural six, not the delivered description's clauses.
  The successor content is exactly what the delivered `StepAt` and `DefAt`
  carry, and it is where the probe stops.
- `archive/rud-route/src/L/Condensation.lagda.md:825-855`: the class-carrier
  story `σL`, its witnesses, and the transfers. The equivalence with the
  delivered description is left standing there, and this probe prices why:
  the reconciliation needs the bounded satisfaction leaves.
- `archive/dev/TASKS-archived.md:165` (`[T130]`), `:262` (`[T257]`),
  `:266` (`[T261]`), `:86` (`[T51]`), `:268` (`[T263]`).
- `_build/l3.32-t51-report.md` section 2: the certification is the
  obstruction, not the count. Section 4: the probe design.
- `_build/l3.32-t130-report.md` section 2: the crossing chapter carries the
  structural story and leaves the successor content standing.
- `_build/l3.32-t257-routes.md` section 3.3: `W1p` unchanged; the crossing
  is the supplier, not the transfers.
- `_build/l3.32-t263-fof.md`: the closest prior result. The delivered
  formula graphs are not Delta-0, and the set-level description needs fresh
  bounded clauses. This probe confirms the same at the L-tower's level
  sentence.
- `dev/LESSONS.md:203` (P-i), `:2099` (P-l), `:1005` (D-1), `:1271` (D-10),
  `:1882` (C-12), and the probe rules. No hang occurred, so the P-i decision
  tree was not needed.

## 7. THE PROBE'S FATE

The probe is untracked: `?? src/ProbeLJ12.lagda.md`. `check-probes.py
--check` is clean. Nothing is staged. I did not delete the probe. A later
audit can delete it with `check-probes.py --stale --delete` after the
freshness window passes. The verdict lives in this report.
