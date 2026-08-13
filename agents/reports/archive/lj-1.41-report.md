# LJ-1.41 report: close the eleven remaining row agreements

Status: COMPLETE. Written incrementally per C-22. No commit, no push.
The report uses ASD-STE100.

## 1. THE VERDICT

**TWO OF THE ELEVEN CLOSED: And and Or, both directions,
machine-checked.** The rate is 0.00853 seconds per line, against
DD24's bar of 0.013193. The other nine cannot close as delivered. They
share one blocker: the story's environment hypotheses are weaker than
the machine's `envSetAt`, in a way no site fact and no Delta-0
compatible repair fixes. The blocker is machine-checked. The audit
before instantiation also found and repaired two shared-leaf defects:
the successor-subvalue key and the AllIn body's first binder.

## 2. WHICH ROWS CLOSED AND WHICH DID NOT

**CLOSED, both directions:**

- **And** (`AndAgree`, `src/L/Condensation.lagda.md:3097`): the
  machine's `andClauseAt` against the story's `And.andBndAt`, at the
  class carrier, under the site facts.
- **Or** (`OrAgree`, `:3147`): the same instantiation at tag 3 with
  union.

Both close because the machine's propositional clauses have NO
environment set. The story's frame binds one (E in K with `envHypB2`),
but the operation the machine supplies does not mention E, so the
story's environment hypothesis is extra content the agreement receives
and does not use. The shared module is `PropAgree` (`:2857`), one
assembly with two instantiations.

**NOT CLOSED: Top, Neg, Forall, Exist, Mem, Eq, Imp, AllIn, ExIn.**

Each of the nine has a machine clause that CONSUMES `envSetAt E` as a
hypothesis and a story row that binds E in K and consumes the weaker
`envHyp* E` ("every member of E satisfies the bounded environment
condition"). The machine-to-story direction must produce the story's
body for every E in K with `envHyp* E`; the machine's clause only
supplies the body under `envSetAt E`, and `envHyp* E` cannot supply
`envSetAt E`. The probe `src/ProbeLJ141C.agda` states the substitution
and Agda rejects it: the two satisfactions are different formulas.

The gap is not an index. `envSetAt` is both directions of "E is
exactly the set of environments" with UNBOUNDED quantifiers; the
story's condition is the first direction with K-bounded quantifiers.
The bounded quantifiers cannot be lifted to the unbounded ones by any
site fact, and a Delta-0 witness does not exist for the unbounded
`envSetAt` (the hierarchy's `Δ₀` has no `δ-∀`, no `δ-∃`), so the rows
cannot be made equivalent within the Delta-0 constraint.

## 3. HOW MANY ROWS NEEDED ANYTHING BEYOND THE SHARED ASSEMBLY? (DD4, D-29.)

**ZERO of the two closed rows.** And and Or are the same module
instantiated twice; nothing row-specific was written. The E-extension
transfers inside `PropAgree` (the second subvalue and the operation
cross the inserted E slot) are shared between the two rows.

The honest DD4 measure is the other way, as it was for `[LJ-1.40]`:
the BLOCKER for the nine unclosed rows is itself in the shared layer.
The environment hypotheses (`envHypT`, `envHypU`, `envHypB2`,
`envHypB2T`, all at `src/L/Condensation.lagda.md:587-650`) share one
shape, and that shape is weaker than the machine's `envSetAt`. The
shared layer carries the defect again.

## 4. DID YOU AUDIT THE SHARED ASSEMBLY BEFORE INSTANTIATING IT? Say how.

YES. Three probes attempted the riskiest leaf transfers before any row
was built. Each failure names a defect, in the style of
`ProbeDD25E3`:

1. `src/ProbeLJ141A.agda`: the successor-subvalue transfer
   `subValSuccB` against `subValSuccAt`. Agda rejected it with
   `fst z₁ != fst (lookup ar γ)`: the story's second-layer reader
   demanded the arity slot while the machine's witness is the
   successor element. The story's `subValSuccB` read the subformula's
   key at the SAME arity (`pr ar a`) instead of the SUCCESSOR arity
   (`pr (sucV ar) a`). REPAIRED at `:473-478` (one index: `suc zero`
   for `suc (suc ar)`), and the probe now checks GREEN, which is the
   machine-checked confirmation that the repaired transfer closes.
2. `src/ProbeLJ141B.agda`: the AllIn body's first binder. Agda
   rejected it with `K != B`: the story's `bndBodyAll` read the term's
   value at the FIRST B-MEMBER, while the machine's `bodyAll` reads it
   at an unbounded value binder, and the row's own comment says the
   value lies in K. REPAIRED at `:1013` (the first binder moves from
   `suc^8 B` to `suc^8 K`), which matches the parallel `bndBodyEx`
   and closes the AllIn body against the machine.
3. `src/ProbeLJ141C.agda`: the environment hypothesis. Agda rejects
   the story's `envHypT E` where the machine needs `envSetAt E`. This
   is the nine-row blocker of section 2, and it is NOT repaired: it is
   structural, not an index.

The two repairs are corrections to match the machine, not weakenings.
Both were made before any agreement was instantiated, per D-29.

## 5. THE NUMBER

2,498 in-fence lines at HEAD; 2,805 after this block. The delta is
307 lines: the two shared-leaf repairs (2 lines), the leaf-transfer
machinery (`SubValB2T` `:2787`, `SubValSuccB2T` `:2806`, `OpTransfer`
`:2834`), and the binary-propositional agreement (`PropAgree` `:2857`,
`AndAgree` `:3097`, `OrAgree` `:3147`).

## 6. SECONDS AND RATE

Cold runs, one process each, at `GHCRTS="-A64m -I0 -M8g"`, the
master's own interface moved aside, dependencies warm:

| run | user s | wall s |
|---|---:|---:|
| baseline at HEAD | 12.39 | 13.64 |
| final | 23.93 | 24.47 |

The final rate is 23.93 / 2,805 = **0.00853 seconds per line**,
against DD24's bar of 0.013193, at 0.65 of the bar. The cone, measured
with the imports-only control `src/ProbeLJ141Ctrl.agda` in the same
session, is 1.34 seconds of user time. The net content cost is about
22.6 seconds over the 2,805 lines, which is 0.00806 seconds per line.

C-31 framing: the GCH side's whole budget is 99.6 to 147.7 seconds
(`dev/ledger.toml:305`). This master's whole measured cost is about
23.9 seconds, about 0.16 to 0.24 of the budget's low end.

## 7. DID YOU NEED A PLACEMENT ANYWHERE?

NO. No `absFo`, no `placeFo`, no constant vector and no appended
environment appear anywhere in the repairs, the transfers or the
agreements. P-u holds.

## 8. WHAT CONDENSATION STILL OWES

The nine environment rows' agreements. Each needs the environment
hypothesis to reach the machine's `envSetAt`; within the current
Delta-0-bounded design that is impossible, so the repair is a design
decision: either the story's environment condition becomes the
machine's `envSetAt` (and the rows' Delta-0 witnesses and Sigma-1
certificates are re-laid around it), or the machine-to-story direction
is accepted as one-way and the bridge is built story-to-machine only.
The orchestrator should rule on that before the next dispatch.

The site facts of the closed rows (the tag columns, the codes and
values in K, K's transitivity, the ambient environment set, the
subvalues in K, the extended environments in K) are hypotheses of the
agreement modules. Proving them at the class carrier is the next
block's work.

`[LJ-1.7]` is next.

## 9. LITERATURE USED

`dev/literature/devlin-II5.md`, Step C. Devlin asserts absoluteness
where this block proves a decode, so the book cannot price these rows.
Spent one line, nothing more.

The errata: NOT read. WHY NOT: `[LJ-1.14]` verified they do not cover
Chapter II section 5, and the brief rules out re-checking them.

## 10. ARCHIVE USED

`_build/lj-1.40-report.md`, whole. Took the closed list, the Bot row
as the pattern (`src/L/Condensation.lagda.md:2610-2638`) and the
site-fact bundle as hypotheses.

`src/L/Condensation.lagda.md`, whole, as committed. Took the row
formulas, the frames, `BotAgree`, `EnvB2T`, `TmVal`, the shapes and
the environment hypotheses.

`_build/lj-1.38-review.md`, whole. Took the defect analysis and the
caveat that the per-row claims beyond the Mem row were index
arithmetic, not machine-checked. This block's audit found exactly the
kinds of defects the review's method could not see.

`src/ProbeDD25E1.agda`, `src/ProbeDD25E2.agda`,
`src/ProbeDD25E3.agda`, whole. Took the vacuity countermodel, the
frame-transfer shape, and the red-control style the three new probes
follow.

`src/L/Coding/Model.lagda.md`, whole. The machine, which is correct.
The clauses at `:1117-1990`, the subvalue readers at `:817-845,
:1405-1434`, the environment at `:442-530`, the term value at
`:1686-1738`, the atoms at `:1735-1800`, the bounded quantifiers at
`:1855-1930`.

`dev/LESSONS.md`, the sections the build rules name. D-29, C-35 and
the audit-first discipline decided the order of this block: probe
before instantiate, and the probes found two shared defects and one
structural blocker before any row was built.

## 11. WHAT I AM NOT SURE OF

1. The nine environment rows' story-to-machine directions. The
   analysis says they close (the story's content supplies the bounded
   subvalues and the machine's hypotheses supply the memberships), but
   only And and Or are machine-checked. The report's claim is limited
   to what is checked: the machine-to-story directions cannot close.
2. The right repair for the environment hypotheses. Two options exist
   (section 8) and the choice is the orchestrator's; the report prices
   neither.
3. The site facts' provability at the class carrier. The agreements
   take them as hypotheses, exactly as `[LJ-1.40]` did. Whether each
   fact is provable is the next block's work.
4. The seconds are one cold run at the final state. The earlier flat
   pair at HEAD (12.39 and 12.53 across the two-leaf repair) and the
   single final run (23.93) bracket the added machinery at about 11.4
   seconds for 307 lines, which is the agreement content's own rate of
   about 0.037 seconds per line, well inside the measured range for
   instantiation content.
5. Whether the environment transfer machinery (`EnvB2T`, and the three
   layout instances the brief expected) is needed at all. The closed
   rows do not use it, and a repaired environment hypothesis that
   matches the machine's `envSetAt` would not need it either. This is
   a question for the repair design, not a delivered claim.
