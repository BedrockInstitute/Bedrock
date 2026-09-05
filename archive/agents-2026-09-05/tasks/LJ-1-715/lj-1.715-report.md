# LJ-1.715 report: the merge lemma, landed in `src/` where the family has a name

## HEAD

head_slot: coder
machine: shared
agda_tier: heavy
task: LJ-1.715
obligation: agents/tasks/LJ-1-715/Probe715.agda::bound2-in-limit
verdict: **GO.** `bound2-in-limit` is proved and landed in
`src/L/Ordinal.lagda.md:221-229`, with the limit notion it needs
(`IsLimit`) at `src/L/Ordinal.lagda.md:205-211`. `bound2` itself is
untouched; the change is 33 added lines, one fence, no prose block.
The mirror statement in `agents/tasks/LJ-1-715/Probe715.agda` closes
through the src lemma and carries, as a second theorem, the same route
measured at the small layer and the 710 frame. Every `.agda` under the
task home typechecks: `runs/ordinal-final.out` (src master, EXIT=0,
0.80 s warm), `runs/probe715.out` (EXIT=0, 0.82 s),
`runs/diag-paren.out` (EXIT=0, 0.77 s). `make check` was not run: the
gate belongs to the program at commit time, and this pane's heavy
caliber is not the whole-tree caliber.

## 1. WHAT THE DISPATCH BUILT

Two things in `src/L/Ordinal.lagda.md`, both additive, in one new fence
after `bound2`'s, before `## Members`:

1. `IsLimit` (`:205-211`), the 710 predicate transcribed into the
   chapter: `IsOrd α`, successor closure, and small-family union
   closure stated at the chapter's structure membership. The union
   clause quantifies over the family, so it accepts any presentation of
   the union set; that is the presentation-honesty the proof below
   spends. The name follows the chapter's `IsOrd` family
   (`dev/STYLE-agda.md`, the registered `Ord`/ordinal precedent); no
   glossary entry was added, and none may be by this slot.
2. `bound2-in-limit` (`:221-229`), the brief's statement verbatim over
   that notion. The proof is four lines: apply the limit's union clause
   at `X := Lift Bool` with the family argument left a HOLE, and case
   the membership family on the two boolean indices, where each branch
   is the limit's own successor clause applied to the corresponding
   member.

And the mirror, `agents/tasks/LJ-1-715/Probe715.agda`: the obligation
stated verbatim over the exported `IsLimit`, discharged by the src
lemma; plus `bound2-in-limit-small`, the same proof at the small
library membership over the probe's own clauses, measuring that the
proof's mechanism is the mechanism and not a layer accident.

## 2. THE LADDER, MEASURED

The brief's premise 4 said the cure works "where the family has a
name". Measured, that phrase needed two corrections before the lemma
closed, and both corrections are findings the next brief will need.

| id | question | verdict | evidence |
|---|---|---|---|
| mini-scope | is `bound2`'s where-lifted family referenceable IN `src/`, from a sibling definition in the same module? | NO. `bar.f` is NotInScope even from a sibling; Agda lifts a clause's where block to a module private to the clause | runs/mini-scope.out, `[NotInScope]`, EXIT=42, 0.06 s |
| diag-bare-union | does the union clause stated BARE as `⟨ ⋃ (sett X f) ∈ˢ α ⟩` elaborate? | NO, and for a NEW reason, a parse fact: the union symbol is `infixr 9` and the structure membership is `infix 20`, so in prefix position the union swallows the whole membership as its argument; the checker then reports `[UnequalTerms]` `V ℓ !=< Σ (Type ℓ) _` | runs/diag-bare-union.out, EXIT=42, 0.77 s |
| diag-paren | does the parenthesized spelling `⟨ (⋃ (sett X f)) ∈ˢ α ⟩` elaborate, with the union also green on the right of the membership? | YES, both | runs/diag-paren.out, EXIT=0, 0.77 s |
| ordinal-final | does the delivered src master check in place? | YES | runs/ordinal-final.out, EXIT=0, 0.80 s warm |
| probe715 | does the mirror close, and does the hole route also close at the small layer over the probe's own clauses? | YES, both theorems | runs/probe715.out, EXIT=0, 0.82 s |

**The mechanism, stated for the next brief.** With the family argument a
hole, the elaborator solves it from the RESULT-TYPE constraint: the
goal's head normalizes to a union over `bound2`'s where-lifted family,
and a meta with no arguments is solved by whole-term assignment against
it, no pattern unification involved. The two branch obligations,
blocked on that hole while it was unsolved, retry after the solve and
close by iota at the concrete constructors, where the internal family
is `sucV σ₁` and `sucV σ₂`. Nothing on the right side is ever named or
written. This is a SIXTH route past the naming wall, after the five
710 enumerated and declined (`agents/tasks/LJ-1-710/review-of-bound2-in-limit.md:29-51`,
the five-way enumeration upheld twice at `:49-51`): those five all
required the right side to be NAMED or WRITTEN; the hole lets the
elaborator name it. 710's t-e1 failed because it instanced the clause
at a WRITTEN family, a rigid symbol, which the solver can never match
(`agents/tasks/LJ-1-710/runs/t-e1.out:5-9`). Measured here at both
layers before this report claims it.

## 3. W3, THE WIDEST UNMEASURED TERM, ANSWERED

The brief asked whether the union-closed limit notion already exists in
`src/` or must be stated here. Measured answer: it must be, and it now
is. A sweep over `src/` found no limit predicate over ordinals with a
union-closure clause; the nearest names are unrelated (`Limit` in
`src/L/Choice/Finite.lagda.md:984-985` is a code-stage pair,
`LimitOrdAt` in `src/Everything.lagda.md:852` is object-language
order content). `IsLimit` is therefore stated in the lemma's own fence
in `src/L/Ordinal.lagda.md:205-211`, transcribed from the approved 710
frame (`agents/tasks/LJ-1-710/Probe710.agda:67-90`, Section 1) with the
membership moved to the chapter's structure layer, per the chapter's
own idiom (`bound2`'s statement is written there; the small layer glues
to it pointwise by `∈∈ₛ`, `src/V/Model.lagda.md:76-82`). One notion,
one home, exported public; the probe imports it and holds no copy.

Price came in under the 40-to-120-line estimate: the fence is 33 lines
(`git diff --stat`), of which 13 are comments.

## 4. W2 ANSWER

The mathematics is written once at a generic carrier. `IsLimit`'s
closure clauses are stated for arbitrary index types and arbitrary
families; `bound2-in-limit` instantiates them at `Lift Bool` and at the
family `bound2` happens to lift; the probe duplicates nothing, it
imports the notion and forwards to the proof. No second copy was
funded anywhere, and no deadline conflict arose, so nothing was
weakened: the statement landed exactly at the brief's bracketed shape,
with both memberships and the limit's ordinality carried in the type
(the ordinality of `α` is carried but not consumed by the proof, as in
the 710 skeleton; the merge membership needs only the two closure
clauses).

## 5. HANDOFF

- **GO unblocks `[LJ-1.705]` and `[LJ-1.711]` as the brief projected.**
  `bound2-in-limit` is importable under the tree's explicit-`using`
  discipline; no dependent does a bare open of `L.Ordinal` (measured by
  sweep), so the two new exports cannot clash downstream.
- **The sixth route generalizes, and it is now measured twice.** Any
  wall of the shape "the goal set is a union over a family nothing can
  name" yields to: clause-hole at the family slot, result-type solve,
  branch retry at concrete indices. It cost 710 three dispatches
  (`agents/tasks/LJ-1-710/review-of-bound2-in-limit.md:51`); the
  lesson worth keeping is that a NO-GO on a written family is not a
  NO-GO on the clause.
- **Two parse facts about this tree's notation are now on file**: a
  where-lifted name is NotInScope even to a sibling in the same module
  (runs/mini-scope.out), and `⋃_` at `infixr 9` swallows a looser
  membership to its right when written bare (runs/diag-bare-union.out;
  the chapter's own `union-spec` already parenthesizes,
  `src/V/Model.lagda.md:96`). Writers of membership-at-a-union
  statements should parenthesize by default.
- `dev/LESSONS.md` candidates, for the owner to rule, not for this
  return to write unilaterally: the hole-and-retry route (with both
  measurement sites), and the `infixr`-swallowing parse trap.

## 6. PRICE

| item | measured |
|---|---|
| src master, delivered, warm | 0.80 s, EXIT=0 (runs/ordinal-final.out) |
| probe, delivered | 0.82 s, EXIT=0 (runs/probe715.out) |
| negative controls | 0.06 s and 0.77 s, EXIT=42 (runs/mini-scope.out, runs/diag-bare-union.out) |
| green control | 0.77 s, EXIT=0 (runs/diag-paren.out) |
| brief estimate | 40 to 120 lines |
| src lines added | 33 (13 comment), `git diff --stat` |
| in-fence lines added | 30 non-blank, counted by eye over the one new fence |
| caliber | `-A64m -I0 -M4g`, heavy, set on the pane by the program, never set here |
| heap wall | none; the heaviest single check was the src master at under 1 s |
| `bound2` shape | untouched; no clause, call site or statement edited |
| survey gate | `check-survey-quotes.py LJ-1-715` clean, output pasted in the return |

No number above is quoted under any other caliber than the pane's. One
Agda process per run throughout; the runs were taken sequentially.

## ARCHIVE USED

- `archive/dev/DD-archived.md`: declined, not read. The governing clauses for this dispatch live in `AGENTS.md`, the slot file and `dev/LESSONS.md`; no archived ruling was searched for and none was needed.
- `archive/dev/ORCHESTRATION.md`: declined, not read. The report form this return follows is the live one in `agents/README.md` and the precedent task record; the archived orchestrator rules do not bear on a proof landing.
- `archive/dev/PLAN-archived.md`: declined, not read. No planning question arose; the brief's scope was executed as named.
- `archive/dev/STATUS-archived.md`: declined, not read. Standing status lives in `dev/pod/screen.toml`, which the program injected.
- `archive/dev/TASKS-archived.md`: declined, not read. The predecessor record this task needed is the LIVE 710 directory (`agents/tasks/LJ-1-710/`), not the archived index.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:24` "| 2 | Devlin 2.6 | `G(f,α) = ∃w[K(w, ⋃ran(f)) ∧ F(w,f,α)]` |". Read. Confirms the consuming context the GO feeds: the staging formula's every branch merges the sequence slots through `⋃ran(f)`, which is exactly the membership `bound2-in-limit` now supplies from `src/`.
- `dev/literature/devlin-errata.md`: declined, not read. No classical text claim enters this deliverable; the D-10 truth side was settled in the 710 record, which this return leans on and does not reopen.
- `dev/literature/glossary-review-2026-08.md`: declined, not read. No new term is proposed; `IsLimit` follows the registered `IsOrd` code-name precedent in `dev/STYLE-agda.md`, and the glossary protocol forbids this slot from adding entries anyway.
- `dev/literature/rudimentary-functions.md`: declined, not read. No rudimentary-function content is touched by an ordinal-bound lemma.
- `dev/literature/formalizations-landscape.md`: declined, not read. The return compares nothing to other formalizations; its evidence is entirely this tree's elaborator behavior, measured in `runs/`.
