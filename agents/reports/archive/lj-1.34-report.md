# LJ-1.34 report: the certificate story against the machine

Status: COMPLETE. Written incrementally per C-22. Untracked probes, no
commit, no push. The report uses ASD-STE100.

## 1. THE VERDICT

**NO-GO. The measured rate is 0.436 seconds per line.** The gate is NO-GO
at or above 0.05. The rate is 8.7 times the NO-GO bar and 33 times the GO
bar. The next condensation block cannot fund on this shape.

The number comes from two flat cold runs of `src/ProbeLJ134.agda`: 73.75
and 74.40 seconds of user time over 170 non-blank non-comment lines. The
pair is flat under the noise rule: the delta is 0.9 percent.

The certificate does not close either. Section 2 gives the machine
evidence.

## 2. IS THE STORY Δ₀ NOW?

NO. Two independent obstructions stand.

Obstruction 1 is the leaf content. The story's DefAt leaf is bounded at
the two existentials, but the leaf CONTENT is the delivered `DefBody`
(`src/L/Coding/Powerset.lagda.md:437`). Its leaves carry unbounded
quantifiers. `isCodeAt` is `keyArityAtL` under an unbounded existential
(`src/L/Coding/CodeSet.lagda.md:135-136`), with `hasWitnessAt` under
another (`:240-241`). `satGraphAt` is the graph frame under three
unbounded existentials (`src/L/Coding/Graph.lagda.md:191`,
`src/L/Coding/Model.lagda.md:104-112`). `DefinesAt` is an `extAt` over an
unbounded existential (`src/L/Coding/Powerset.lagda.md:217-219`). The
Delta-0 data has no constructor for an unbounded quantifier
(`src/FOL/LevyHierarchy.lagda.md:47-57`).

The failing certificate is in `src/ProbeLJ134Cert.agda`, 29 lines. Agda
rejects it with this error:

```
∃̇∈ _t_16 _φ_17 !=
keyArityAtL lem (suc zero) 1 ∧̇
hasWitnessAt lem (sh3 lem w) (suc zero)
of type Formula S (suc (suc (suc n)))
when checking that the inferred type of an application
  Δ₀ (∃̇∈ _t_16 _φ_17)
matches the expected type
  Δ₀ (isCodeAt (suc zero) (sh3 lem w))
```

The first conjunct of the leaf is not an `∃̇∈` shape. The bound term for
the code does not exist. This is the same wall `[LJ-1.2]` reported
(`_build/lj-1.2-gate.md:28-35`), now measured at the decode site.

Obstruction 2 is the story's own `extAt` wrappers. The clause and the
DefAt leaf are `extAt` forms (`src/L/Coding/Model.lagda.md:662-664`).
Each is two unbounded universals. The Delta-0 data has no constructor for
them either.

The template certificate closes. `WitCert.Δ₀-wit-tmpl` proves the witness
SHAPE is Delta-0 for any Delta-0 body (`src/ProbeLJ134.agda:104-110`).
The concrete certificate is the template applied to the body. The missing
premise is `Δ₀ (StepStory.BodyB v b f)` (`src/ProbeLJ134.agda:112-116`).
That premise is the bounded satisfaction substrate. The substrate is the
bounded object-level description of the code set and the table
(`_build/lj-1.2-gate.md:64-76`). It is not delivered.

So the answer is NO in both halves. Bounding the two DefAt existentials
is not enough. The story is not Delta-0 at the top, and it is not
Delta-0 at the leaves.

## 3. WHAT BOUNDING DefAt COST

The probe is 170 lines. The bounded story is 25 lines. The template
certificate is 13 lines. The leaf agreement, the body agreement and the
decode are about 110 lines.

The seconds are concentrated in the leaf agreement. The cold profile of
`src/ProbeLJ134.agda`:

| definition | ms |
|---|---:|
| `LeafAgree.leaf-in` | 20,922 |
| `LeafAgree.leaf-out` | 20,734 |
| `StepAgree.body-out-lemma` | 8,887 |
| `StepAgree.body-in-lemma` | 8,845 |
| `BodyAgree.body-out` | 6,702 |
| `BodyAgree.body-in` | 6,628 |
| `StepAgree.wit-in` | 17 |
| `StepAgree.wit-out` | 13 |
| `LeafAgree.add` | 11 |
| miscellaneous, the import cone | 1,259 |
| total | 74,025 |

The leaf agreement pair is 41.7 seconds, 56 percent of the total. The
body agreement pair is 31 seconds.

The cost is P-l's signature. The leaf agreement's types name the built
`DefAt` satisfaction and the built `DefAtB` satisfaction. The elaborator
unfolds the built `DefBody` tree while checking them, about 21 seconds
per direction. The proof itself never pattern-matches the content. The
type does the unfolding.

This is the opposite character from the bound-drop layer. `[LJ-1.33-R]`
measured the abstract-body layer at 34 ms
(`_build/lj-1.33-review.md:29`). There the body was a variable, so
nothing unfolded. Here the leaf agreement must name the delivered leaf,
so the built tree unfolds per use.

## 4. COLD SECONDS AND LINES

Two cold runs of `src/ProbeLJ134.agda`, one Agda process each, quiet
machine, at `GHCRTS="-A64m -I0 -M8g"`. Dependencies were warm through
the interface cache under `_build/2.8.0/agda/`. The probe's own interface
was moved aside
before each run. No interface ever sat beside a source.

| run | user s | wall s |
|---|---:|---:|
| 1 | 73.75 | 75.18 |
| 2 | 74.40 | 76.07 |
| mean | 74.08 | |

The probe is 170 non-blank non-comment lines. The line convention is
`grep -v '^[[:space:]]*$' | grep -vc '^[[:space:]]*--'`.

Rate: 74.08 / 170 = 0.4358 seconds per line.

The certificate probe `src/ProbeLJ134Cert.agda` is 29 lines. It fails in
1.15 seconds of user time. The failure is the evidence, not a number.

## 5. DID IT NEED A PLACEMENT?

NO. The story, the certificate and the decode stand at variable slots.
No `absFo`, no `embed`, no placed Delta-0 enters. The certificate fails
for syntactic reasons, not for a carrier reason. P-u held: nothing
needed certifying before a placement, because no placement exists.

## 6. THE PRICE OF THE NEXT BLOCK

On my numbers the block does not fund.

| piece | lines | rate | seconds |
|---|---:|---:|---:|
| the decode skeleton, witness level | 30 | 0.001, MEASURED | 0.03 |
| the leaf agreement and body agreement | 110 | 0.66, MEASURED | 73 |
| the Delta-0 certificate | not buildable today | | |
| the bounded satisfaction substrate | 2.7 to 3.0k+, SURVEY | | |

The block needs a re-shape before funding. The re-shape must stop the
leaf agreement from naming the built `DefAt` satisfaction in a checked
type. One candidate is a generic leaf layer with the body abstract, the
way `[LJ-1.33-R]` did the outer layer. The instantiation still names the
built satisfaction, so P-l forbids pricing it by analogy. I did not
measure it.

The certificate half needs the substrate before any rate exists. The
substrate is the bounded table's remaining eleven clauses and the bounded
code description (`_build/lj-1.2-gate.md:64-76`). It is not a miniature.

## 7. DD4

The certificate has a template half and a per-tower half.

The shape is template. The witness-level Delta-0 recursion closes for any
body with a Delta-0 certificate (`src/ProbeLJ134.agda:104-110`). The
same shape serves every clause and every tower.

The content is per-tower. The bounded leaves are the code description,
the table and the defines relation. They are the Def tower's syntax.
D-26 predicted this: the Def stage is a definable power, so its level
story runs through codes and satisfaction (`dev/LESSONS.md:1676`). The J
tower's stage carries generation data, so its bounded clauses are
structural (`src/L/Condensation.lagda.md:142-150`).

The measured cost is neither half. It is the shared machine's built tree.
The leaf agreement's cost is the elaborator unfolding the delivered
`DefBody`, which both towers share. A template leaf layer would buy the
other tower the expensive half only if the instantiation stayed opaque.

## 8. LITERATURE USED

`dev/literature/devlin-II5.md`, Step C (`:209-256`). Took the Sigma-1
form with a Sigma-0 matrix, and the bounded Def-step inside the matrix.
Devlin's bound is the concrete set K(u), the finite sequences over the
formula set, the variables and the members of u. The project's analogue
is the bounded satisfaction substrate. The book asserts absoluteness
where the formal proof must prove a decode, so the book cannot price
this row. One line, and nothing more was spent.

`dev/literature/devlin-errata.md`. NOT read. WHY NOT: the brief rules
out re-checking it, and `[LJ-1.14]` verified it does not cover Chapter
II section 5 (`_build/lj-1.14-report.md:107-108`).

## 9. ARCHIVE USED

`_build/lj-1.33-review.md`, whole. Took the caveat at `:198-212`, the
2x2 at `:70-84`, the profile at `:64-68`, the not-sure list at
`:238-247`.

`_build/lj-1.33-report.md`, whole. Took the proxy diagnosis at
`:259-262`, the cost profile at `:89-96`, the DD4 placement at
`:181-192`.

`_build/lj-1.2-gate.md`, whole. Took the failure mechanism at
`:28-35`, the substrate price at `:64-76`, the verdict at `:14-16`.

`_build/lj-1.28-report.md`, whole. Took leg D at `:95-100`, the
residue price at `:128-136`, the certificates at `:118-120`.

`_build/lj-1.5-report.md`, whole. Took block 1's rate at `:11-14` and
the DD4 split at `:117-138`.

`src/L/Coding/Powerset.lagda.md`: `DefBody` at `:437`, `DefAt` at
`:442`, `isCodeAt` at `:297`, `DefinesAt` at `:217`.

`src/L/Coding/CodeSet.lagda.md`: `keyArityAtL` at `:135-136`,
`hasWitnessAt` at `:240-241`.

`src/L/Coding/Graph.lagda.md`: `satGraphAt` at `:191`.

`src/L/Coding/Model.lagda.md`: `extAt` at `:662-664`, the graph frame
at `:104-112`.

`src/L/Coding/Sequence.lagda.md`: `StepBody` at `:113`, `StepAt` at
`:119`, the projections at `:217-229`.

`src/L/Condensation.lagda.md`: the Clause module at `:52-195`, the
Delta-0 witnesses at `:142-150`.

`src/FOL/LevyHierarchy.lagda.md`: the Delta-0 data at `:47-57`.

`dev/LESSONS.md`: P-l at `:2305`, P-m at `:2460`, P-n at `:2483`, P-t
at `:2601`, P-u at `:2908`, D-1 at `:1038`, D-10 at `:1316`, D-26 at
`:1676`, C-32 at `:2947`, C-33 at `:2987`.

## 10. WHAT I AM NOT SURE OF

1. The measured rate prices the top-bounded story, not the fully
   bounded certificate story. The top-bounded story is the shape that
   typechecks today. The fully bounded story needs the substrate, whose
   own decode is unmeasured and would add to the row.
2. A different leaf-agreement shape might dodge the P-l wall. A generic
   leaf layer with the body abstract would move the unfolding to the
   instantiation. P-l forbids pricing it by analogy, and I did not
   measure it.
3. The leaf bound facts are hypotheses, not proofs. The bound
   construction, the carrier facts row, is still owed, exactly as it
   was in `[LJ-1.33]`.
4. One clause measured. The approximation and graph clauses have
   different bodies. Their leaf agreements may cost differently.

## 11. PROBES BUILT

All untracked, all thrown away per D-1.

| file | lines | what it measures |
|---|---:|---|
| `src/ProbeLJ134.agda` | 170 | the bounded story, the template certificate, the decode |
| `src/ProbeLJ134Cert.agda` | 29 | the failing concrete certificate |
