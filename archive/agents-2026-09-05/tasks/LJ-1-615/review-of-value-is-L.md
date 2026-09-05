# review of `value-is-L`: the recovered second factor needs `TransferL`, the factorization does not split paid from unpaid, and the stop is the one the brief funded in advance

## VERDICT

**THE TERM IS NOT SUPPLIED, BECAUSE THE RECOVERED STATEMENT NEEDS THE
AMBIENT-TO-INNER MOVE, AND THAT MOVE IS `TransferL`'S CONTENT.** The
obligation is ONE term, `value-is-L : ValueIsL`, the second factor of
`[LJ-1.611]`'s recovered `ambientOnly-from : TransferL → ValueIsL →
AmbientOnly`. The meter says the name is absent as designed:
`agents/tasks/LJ-1-615/Probe615.agda::value-is-L` returns `missing
exit=42 ... [NotInScope]`, `1 UNRESOLVED of 1`, `probe_red=False`
(witness run, 1.50 s). The probe itself is GREEN and carries no hole
(`agents/tasks/LJ-1-615/runs/p-4-forced.out`, exit 0, 8.78 s, peak
580,648,960 bytes, forced recheck of the delivered file).

This is the brief's own pre-funded outcome: "**IF `ValueIsL` TURNS OUT
TO NEED `TransferL`, SAY SO AND STOP.** That would mean the
factorization does not split the way its author thought, and it would
put row 3 back into the unpaid direction." It needs `TransferL`. Row 3
is back in the unpaid direction. The brief's premise for tractability
("`ValueIsL` does not [run the unpaid direction], and that is the whole
reason this brief takes it") does not survive the recovery: the
recovered factor's HYPOTHESIS is the ambient reading of the graph at an
arbitrary ambient environment, and consuming an ambient hypothesis is
exactly the direction `[LJ-1.533]` measured as unpaid.

## THE RECOVERY, AND WHY THE FIRST READING WAS WRONG

From `[LJ-1.611]`'s report ALONE the factor reads as the INNER
determination: the report gives the arrow type
(`agents/tasks/LJ-1-611/lj-1.611-report.md:197-199`) and the words "the
value's constructibility"
(`agents/tasks/LJ-1-611/review-of-graph-ambient.md:90-92`), and an arrow
type underdetermines the split. That reading states, inhabits, and even
recomposes a factorization at today's carrier (measured: `runs/w3-1.out`,
`runs/w3-2.out`, `runs/p-1.out`, `runs/p-2-forced.out`, all green, all
kept). It is WRONG, and the report itself says why: "**Neither factor
was delivered there**", while the inner `Lset-only` WAS delivered there
("the delivered inner `Lset-only`",
`agents/tasks/archive/L3-32-T70/l3.32-t70-report.md:36-37`). A factor
that was free cannot be the factor the report says was missing.

The C-42 sweep (this task's report, `## C-42, THE SWEEP`) surfaced the
retired route's own task records, which quote the type literally and
agree five times over
(`agents/tasks/archive/L3-32-T51/l3.32-t51-report.md:55`,
`agents/tasks/archive/L3-32-T144/l3.32-t144-report.md:20`,
`agents/tasks/archive/L3-32-T130/l3.32-t130-report.md:69`,
`agents/tasks/archive/L3-31-IVPROBE/l3.31-ivprobe-report.md:222`, and
the blocker measurement at
`agents/tasks/archive/L3-32-T70/l3.32-t70-report.md:38-39`):

    ValueIsL = (v b : S) → IsOrd b
             → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt {2} zero (suc zero) ⟩
             → ⟨ isL v ⟩

with `S` the ambient carrier. **The second factor is the AMBIENT one:
the ambient satisfaction of the graph implies the VALUE is
constructible.** No git history was read; the archived task records are
records, not git, and the sweep is this slot's own law (C-42).

## THE STATEMENT AT TODAY'S CARRIER

`agents/tasks/LJ-1-615/Probe615.agda:131-134`, the W3 type letter for
letter (`runs/W3.agda:66-69`, green alone at `runs/w3-3.out`):

    ValueIsL = (v b : SV.S) → IsOrd b
             → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt zero (suc zero) ⟩
             → ⟨ isL v ⟩

`v` and `b` are ambient sets (the satisfaction's environment sits at
the structure's carrier, `src/FOL/Semantics.lagda.md:91`), `IsOrd` and
`isL` are today's at the ambient carrier (`src/L/Constructible.lagda.md`),
and the formula is TODAY'S rebuilt graph (`src/L/Coding/Sequence.lagda.md:291-292`,
opened at `:349`; the arity-2 instance carries the name `LsetGraph`,
`:353-354`). **That is the whole move: the shape is unchanged from the
retired form, and the formula under it is today's.** The retired
chapter's `LsetGraphAt` is gone with its route; today's carries the same
slots and the same role (the tower's graph, `Lset-only`'s subject).

## DOES IT NEED TransferL

**YES.** The hypothesis is the ambient reading at an arbitrary ambient
environment (every existential ranges over every ambient set,
`src/FOL/Semantics.lagda.md:96`; the graph's own outer binder is
unbounded, `src/L/Coding/Sequence.lagda.md:292`), the conclusion is an
inner fact, and every delivered road between the two is closed: the
transfer machine covers Δ₀/Σ₁/Π₁ only (`src/FOL/Absoluteness.lagda.md:80-121`),
the graph is none of the three (its approximation conjunct carries
unbounded
universal quantifiers in the definition itself,
`src/L/Coding/Sequence.lagda.md:287-292`, documented at
`src/L/Condensation.lagda.md:2461`), the
bounded restatement's leaf adequacy is conditional on the certificate
frame's site facts (`src/L/Condensation.lagda.md:7216-7306`, `[LJ-1.611]`'s
finding), and the determination lemma is inner-only
(`src/L/Hierarchy.lagda.md:333-335`). The site of the need is the
composition itself: `Probe615.agda:191-198` rebuilds the retired
factorization green with both factors as hypotheses, and the second
factor's whole job there is to carry the ambient VALUE into the class
carrier so the transfer can hand the inner environment to the free
inner determination; without the ambient-to-inner move there is nothing
for `isL` to be extracted FROM. The retired route measured the same
thing at its own site: "`ValueIsL` has the same single blocker"
(`agents/tasks/archive/L3-32-T70/l3.32-t70-report.md:38-39`).

## WHAT THIS PRICES FOR ROW 3

The `3f5001e` factorization does NOT split into a paid factor and an
unpaid one. Both factors need the ambient-to-inner move: `TransferL` is
the move, and `ValueIsL`'s only delivered route is the move plus
`Lset-only` plus `Lset→isL` (the retired route's own decomposition,
`T70:38-39`). The honest residue is therefore ONE obligation, not two:
the ambient determination of the graph, which is `[LJ-1.611]`'s
`Honest-G-` from the class-carrier side, and which runs in the
direction `[LJ-1.533]` measured as unpaid
(`agents/tasks/LJ-1-533/lj-1.533-report.md:76`). This task does NOT
claim `ValueIsL` is FALSE: at the adequate matrix the ambient
determination is true classically (Devlin 5.2 (a),
`dev/literature/devlin-II5.md:95-97`), and the stop is a supply stop.
The truth of the transfer at the DELIVERED matrix stays open, as
`[LJ-1.611]` measured (`TransferL`'s TRUTH is open,
`agents/tasks/LJ-1-611/lj-1.611-report.md:321-322`).

## SCOPE

I wrote only inside `agents/tasks/LJ-1-615/`. Nothing is postulated, the
probe carries `--safe`, the delivered file is green with no hole, and
nothing lands in `src/`. No commit, no push.
