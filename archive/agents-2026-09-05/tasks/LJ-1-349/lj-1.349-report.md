# LJ-1.349 report: DD25 adversarial review of `[LJ-1.348]`'s `witK` refutation

tier: pi (in-harness-subagent-mode), the switch's ADVERSARIAL row (`herdr` /
`pi` / `glm-5.3`). Written incrementally (C-22). Every negative is MEASURED or
INFERRED, in those words. `src/` untouched; nothing landed, nothing repaired.

## 0. VERDICT

**UPHOLD.**

**The refutation holds, at both chapter index forms, and I REBUILT IT MYSELF
rather than take the transcription** (`agents/tasks/LJ-1-349/Refute349.agda`,
exit 0 in 2.48 s, my own transcriptions of both tie types from `src/`, my own
cycle lemma rotated the other way, my own environment). The tag-6 reading is
correct, the premise is inhabited, and the countermodel lives INSIDE the
chapter's intended premise class. The word MEASURED FALSE is right.

**AND MY REBUILD ADDS ONE NEW MACHINE-CHECKED FACT the target did not have.**
`Refute349.agda`, module `Live349`: at the countermodel environment,
`⟨ env ⊨ hasWitnessAt A x ⟩` is INHABITED by the countermodel's own witness
set. `WitnessAgree.out` consumes exactly `hasWitnessAt A x`
(`src/L/Condensation.lagda.md:6709-6710`), so the countermodel is not an
environment outside the chapter's use. **The last escape, 「false only where
the chapter never looks」, is closed, and closed by a term.**

| claim under test | verdict | basis |
|---|---|---|
| tag 6 has a free arity slot | **YES, MEASURED** | twelve disjuncts read and named, section 1 |
| `closedAt` never speaks about tag 6 | **YES, MEASURED** | eight clauses read, tags 2,3,4,5,8,9,10,11, section 1 |
| the countermodel refutes both verbatim chapter forms | **YES, MEASURED** | my `Refute349.agda`, exit 0, section 2 |
| the refuted premise is inhabited | **YES, MEASURED** | my `Live349`, from an arbitrary carrier element |
| the countermodel is inside the `out` premise class | **YES, MEASURED, NEW** | my `Live349.intended`, section 3 |
| 「MEASURED FALSE」 is the right row word | **YES** | section 4 |
| `[LJ-1.344]`'s `shapedAt` blocking is the wrong reading | **YES, MEASURED** | section 5, at its `:186-188` |
| the cure is payable at the call site | **MEASURED FALSE** (site scope read) | `MustFail348` re-run, exit 42, section 6 |
| `graphWitK`'s INFERRED verdict should be measured first | **YES, my recommendation** | section 7 |
| the countermodel is class-free (DD4) | **YES, MEASURED** | my file's names read, section 10 |

**COST.** Five agda invocations of mine plus three re-runs of the target's
probes, longest 2.48 s, floor 0.066 s. No wall. No heap exhaustion. The cap was
never raised. Slot count run before every invocation, always 0.

## 1. THE TAG-6 READING, WITH THE TWELVE DISJUNCTS COUNTED (C-57)

I read `shapes` at `src/L/Coding/Shape.lagda.md:182-187` myself. **Twelve
disjuncts, read and named, none skipped:**

| # | disjunct | relation | what it pins | arity pinned? |
|---|---|---|---|---|
| 1 | `binForm 0 (bothTm A)` | bothTm | payload two term codes at A | **no** |
| 2 | `binForm 1 (bothTm A)` | bothTm | payload two term codes at A | **no** |
| 3 | `binForm 2 noneB` | ⊤̇ | nothing | **no** |
| 4 | `binForm 3 noneB` | ⊤̇ | nothing | **no** |
| 5 | `binForm 4 noneB` | ⊤̇ | nothing | **no** |
| 6 | `unForm 5 noneU` | ⊤̇ | nothing | **no** |
| 7 | `unForm 6 zeroPay` | `var zero ≐ con (numeralL 0)` | payload is `# 0` | **no** |
| 8 | `unForm 7 zeroPay` | same | payload is `# 0` | **no** |
| 9 | `unForm 8 noneU` | ⊤̇ | nothing | **no** |
| 10 | `unForm 9 noneU` | ⊤̇ | nothing | **no** |
| 11 | `binForm 10 (fstTm A)` | fstTm | first payload a term code at A | **no** |
| 12 | `binForm 11 (fstTm A)` | fstTm | first payload a term code at A | **no** |

The frames `unForm k rel = ∃̇ (∃̇ (arityTagAtL 2 1 k 0 ∧̇ rel))` (`:104-105`)
and `binForm` (`:101-103`) bind the arity `N` existentially, and **no relation
column mentions `N`**: `noneB` and `noneU` are `⊤̇`, `zeroPay` speaks only
about the payload, `bothTm`/`fstTm` speak only about payload term codes. So the
arity slot is free at ALL TWELVE tags, and the free slot is easiest to use at
tags 6 and 7, where the payload is pinned to `# 0` and nothing else is asked.
**The target's tag-6 choice is the simplest member of a four-tag family
(0, 1, 6, 7) of closure-free disjuncts; one member suffices.**

I then read `closedAt` at `src/L/Coding/Model.lagda.md:2182-2195` myself:
**eight clauses, read and named**: `andClosedAt` (tag 2), `orClosedAt` (3),
`impClosedAt` (4), `negClosedAt` (5), `existClosedAt` (8), `forallClosedAt`
(9), `allInClosedAt` (10), `exInClosedAt` (11), conjoined at `:2191-2195`.
Each is `∀̇∈ (var C) (... ⇒̇ rel)` (`:2043-2049`), guarded by a tag pattern,
so a clause is vacuous on a member that is not its tag. **Tags 0, 1, 6 and 7
carry no clause. A set whose only member carries tag 6 satisfies all eight
vacuously.** Both readings of the target reproduce from the source.

## 2. THE COUNTERMODEL, REBUILT (the sibling standard)

`agents/tasks/LJ-1-349/Refute349.agda`, **exit 0 in 2.48 s**, floor 0.066 s.
Built from my own reading, not from `[LJ-1.348]`'s file:

- **Both tie types transcribed by me** from `src/L/Condensation.lagda.md:6683-6685`
  and `:7233-7235` (module `Forms`). Both discharge into `Empty.⊥`.
- **My own cycle lemma**, `cyc4`, rotated the other way: the target recursed on
  the accessibility of the chain's first element, mine on the last
  (`Refute349.agda:75-78`). The chain is `b ∈ ⁅b, pr 6 0⁆ ∈ fst c ∈ fst W ∈ b`,
  four steps, refused by `regularityV` (`src/V/Hierarchy.lagda.md:139-144`).
- **The countermodel**: `c := prʟ B (prʟ (numeralL 6) (numeralL 0))` with the
  bound `B := lookup Ki γ` in the free arity slot; `W := pairʟ c c`, the
  L-side singleton. Closedness by refusing each of the eight clauses at its
  own tag; shapedness at the sixth disjunct with `A` never used.
- **Scope identity checked** (the `[LJ-1.345]` discipline): my `⊨` is
  `GM.AbsL.⊨ᵐ`, and `L.Coding.Model`'s `AbsL` is the SAME module the chapter
  opens, `FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`
  (`src/L/Coding/Model.lagda.md:72`, `src/L/Condensation.lagda.md:76`, both
  with `isL` from `L.Constructible` at Model `:44` and Condensation `:25`).
  `closedAt` and `shapedAt` are imported by the chapter from the same two
  modules I import (`:30-31`, `:52-54`). `∈ˢ` at the L structure is
  `fst a ∈ fst b` (`src/FOL/ZFStructure.lagda.md:149`). **This is not a
  refutation of a look-alike.**

**Re-runs of the target's probes, all reproducing**: `Refute348.agda` exit 0 in
1.08 s (cache warm), `MustFail348.agda` **exit 42 in 1.47 s, EXPECTED RED,
unrepaired**, with the error again naming the missing fact
(`fst (lookup xi γ) != fst u ... ⟨ fst u ∈ fst (lookup A γ) ⟩`), `Field348.agda`
exit 0 in 2.13 s. `Floor349.agda`, my own empty module: **0.066 s**, confirming
the target's floor figure and its note that this machine is not the machine
`[LJ-1.346]` and `[LJ-1.344]` measured (C-53).

## 3. NON-VACUITY, RE-CHECKED, AND STRENGTHENED

Three layers, all in my own file:

1. **The premise is a term** at `W`: `Refute349.agda` `premiseW`, all three
   conjuncts built.
2. **The environment hypothesis is inhabited** from an ARBITRARY carrier
   element: `Live349 Any` builds `env := shp ∷ Any ∷ []` and closes `hx-live`
   by computation. The tie is empty at that environment (`empty-here`).
3. **NEW, machine-checked: the chapter's own premise is inhabited there too.**
   `Live349.intended : ⟨ env ⊨ hasWitnessAt (suc zero) zero ⟩` is
   `∣ M.W , M.premiseW ∣₁`, because `hasWitnessAt A x`
   (`src/L/Coding/CodeSet.lagda.md:240-242`) is EXACTLY the existential whose
   body `witK` quantifies over. `WitnessAgree.out` consumes that formula
   (`src/L/Condensation.lagda.md:6709-6710`). **So the countermodel
   environment is one where the module's own entry point has work to do, and
   the tie it needs is empty.** The target argued the neighbouring point by
   counting consumers (zero for `LeafAgree`, re-measured below); this closes
   the question from the satisfaction side, and it is the strongest form of
   non-vacuity available.

**Consumer counts re-measured (C-57).** `grep -rn 'LeafAgree\|WitnessAgree' src/`
returns hits only inside `src/L/Condensation.lagda.md`, ten lines, all read and
named: `LeafAgree` at its declaration `:7224` and four comment lines (`:6192`,
`:7216`, `:7219`, `:7236-7237`), ZERO consumers; `WitnessAgree` at its
declaration `:6680` and ONE consumer, `LeafAgree`'s `module WA` at `:7307`.
The target's section 3.3 reproduces exactly.

## 4. IS 「MEASURED FALSE」 THE RIGHT WORD

**YES. For the statement as written, FALSE is what was measured, and the
target's own limit section is accurate and necessary.**

The tie's type, closed over its module binders, is
`∀ {n} (A x K) (γ : S ^ n) → WitK A x K γ`. A universally quantified statement
is false exactly when some admissible instance has an inhabited premise and a
refuted conclusion. That is what both countermodels give: at `env`, `witK`'s
premise holds at `W` and its conclusion closes a four-step membership cycle.
**「No supplier exists」 is then forced for every instantiation whose `γ` is
generic**, which is what the whole leaf branch is: `LeafAgree`'s `γ` is a
module parameter, `WitnessAgree` is instantiated inside it at that same `γ`
(`src/L/Condensation.lagda.md:7307`), and any eventual theorem instantiating
the branch quantifies over its own `γ`.

What is NOT true, and the target never claimed it, is the siblings' stronger
form 「empty at EVERY `γ`」: where the read slot is no shape at all, the
premise is empty and the tie is vacuously suppliable. The target says this in
its own words at its section 3.2. **The row should keep the qualifier the
target states** (no UNIFORM supplier; empty at the countermodel environments)
**but the headline word FALSE is correct**, and my `intended` term removes the
reading that the countermodel environments are somehow outside the statement's
intended range.

## 5. THE `shapedAt` CONTRADICTION SETTLED: `[LJ-1.344]` IS THE WRONG READING

**The wrong reading is at `agents/tasks/LJ-1-344/lj-1.344-report.md:186-188`:**
「The easy countermodel is closed off: `shapedAt` forces every member of `w'`
to be a shape, so `w'` cannot be the set that produces a membership cycle.」

**The first half is right and the inference is wrong.** `shapedAt C A =
∀̇∈ (var C) (shapes A)` does force every member of `w'` to be a shape. But the
cycle needs no non-shape member: it runs THROUGH a shape's own pair structure.
The shape `c = pr b (pr (# 6) (# 0))` is a legal tag-6 member with the bound
in its free arity slot, and the cycle `b ∈ ⁅b, pr 6 0⁆ ∈ fst c ∈ fst W ∈ b`
uses only the Kuratowski components of `c` and the singleton structure of `W`.
**`[LJ-1.344]` read the definition correctly and drew the wrong consequence,
because it did not ask where the cycle's members come from.**

Two independent corroborations:

- **The delivered prose**, `src/L/Coding/CodeSet.lagda.md:21-27`, the tree's
  own record of this hole: 「nothing in `closedAt` or `shapedAt` constrains the
  arity slot. Shapedness binds the arity existentially and puts no condition on
  it, so a set holding a pair whose first component is not a numeral at all
  satisfies both halves, and the decode has nothing to say about that pair.」
  The countermodel's `c` is exactly 「a pair whose first component is not a
  numeral at all」: its first component is the bound. **If the countermodel
  were wrong, this prose would describe a different hole; it describes the
  same one.** The prose also records that the debt was PAID only in the
  CodeSet composite predicate, by an outer numeral conjunct; `witK`'s premise
  is the unpaid bare half.
- **Two machine-checked countermodels**, the target's and mine, independently
  transcribed.

**A precision the record owes `[LJ-1.344]`:** its narrow table row 「refutable
by `[LJ-1.341]`'s countermodel: MEASURED FALSE」 is defensible read literally
(the `[LJ-1.341]` model used a non-shape member, and that one IS blocked); the
false step is the section 6.1 inference from that row to 「so `w'` cannot be
the set that produces a membership cycle」 and to 「INFERRED that `witK` is
true at the intended instance」. The row must change as the brief says: the
sibling task's `[LJ-1.344]`-derived expectation 「`shapedAt` blocks it」 is
MEASURED FALSE, and the blocking inference is the error, not the definition
reading.

## 6. THE CURE, AND THE CONTROL

`MustFail348.agda` re-run: **exit 42**, error at `MustFail348.agda:59.26-32`
naming exactly the missing carrier membership. The control is fair as a
control: it documents that the site's own closest candidate (the first
conjunct) is refused. **One precision, C-36's**: exit 42 alone measures a
failed offer, not an impossibility. What completes the claim is the scope
enumeration, which I re-did: the site `src/L/Condensation.lagda.md:6717-6721`
binds `w` with exactly `hxw`, `hcl`, `hsh` out of `hasWitnessAt A x`
(`:6712`), and the module's other parameters that could mention `w`
(`codesK`, `unCodesK`, `entryK`, `:6686-6705`) each TAKE
`⟨ fst w ∈ fst (lookup K γ) ⟩` as their own premise, which is the conclusion
`witK` was supposed to feed. **Nothing at the site can pay the cure's
hypothesis without first proving the tie's conclusion.** MEASURED, by reading
the site and the four telescopes. The target's table row is right.

## 7. `graphWitK`: MEASURE BEFORE THE PROJECT BELIEVES IT

The target marks `graphWitK` **INFERRED false** and priced the countermodel at
about 120 lines, unbuilt. **My ruling: the inference is honest but it must not
be banked as false until the countermodel exists with an inhabited premise.**

The reason is this chain's own pivot, stated by `[LJ-1.341]` and `[LJ-1.345]`
both: **a refutation is only a refutation where its premise is inhabited.**
The `graphWitK` premise (`src/L/Condensation.lagda.md:7288-7296`) asks for
FIVE things, and the target inhabited only the second (`closedAt` on `d`,
vacuous on a tag-6 singleton). `domAt`, `appAt` and `twelveAt` are untested at
the proposed `d`, and `twelveAt` is a twelve-clause predicate. If those three
pin `d` (for instance through the one-entry function the target itself
sketches), the countermodel could be blocked in a way `witK`'s never was. The
same gap is why `[LJ-1.344]`'s arity-numeral refutation stayed INFERRED for a
whole task: one clause short of a wall.

**So: the row should read INFERRED until the sibling's or a follow-up's
countermodel is green with its premise term, and the about-120-line price is a
reasonable basis (DD8: the analogous blocks in the same file). I did not build
it either; this review's budget went to the rebuild of `witK`, which was the
gate the project asked for.**

## 8. THE ABORT CRITERION, ANSWERED

UPHOLD. **Three of the six construction ties are then false** (`witK` here,
plus the two arity-numeral conjuncts if the sibling settling them upholds),
and the family finding is route-level: **every `LeafAgree` tie that concludes
a bound membership from closure predicates alone, with the witness or the
arity drawn from an unbounded slot, is false**, because the coding never
bounds the arity slot (`shapes`' existential) and closure speaks at eight
tags only. For the remaining two: `graphWitK` is in the shape at two of its
three conclusions (section 7) and should be measured, not assumed; the four
codes-ties (`wCodesK`, `wUnCodesK`, `gCodesK`, `gUnCodesK`) CARRY
`⟨ fst w' ∈ K ⟩`-style premises per the target's measured extent table and
are outside the refuted shape, so the family has a boundary and the boundary
is named: a bound-membership premise.

## 9. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md:246-251`, read.** **The one line the brief
asks for: a witness drawn from an unbounded existential has NO counterpart in
Devlin's text; his `w` is fixed to `K(u)` by construction** (「the Σ₀ matrix
C(w, v, u) with w = K(u) is the bounded satisfaction substrate」, digest
`:250-251`, primary `dev2.txt:593-630`). `witK` sets that fixed `w` free, and
the countermodel shows what walks in. The target's section 8 reading is
faithful to the digest and I confirm it. WHY NOT the rest: `:236-240` is the
limit-stage union law, not about closure; `:241-244` is the settled `[LJ-1.12]`
Δ₀ question; Step D (`:258` on) needs a definable well-order no `LeafAgree`
tie reaches.

## 10. DD4, WITH THE AXIS NAMED (C-46)

**The axis is AC-AGAINST-GCH**, fixed at `scripts/measure/ledger.py:49-51`,
whose `--reuse` report computes what the AC and GCH closures share.

**The countermodel is class-free, MEASURED by reading MY OWN file's names**:
`pr`, `prʟ`, `pairʟ`, `numeralL`, `⁅_,_⁆`, `regularityV`, `closedAt`,
`shapedAt`, `Acc`. **Not one name mentions AC, GCH, a well-ordering or a
cardinal, and the environment is built from an arbitrary carrier element.**
So the refutation serves the shared chapter as written, at whichever carrier
instantiates it, by one file. **The target's claim that what the task removes
is a false line from the shared side is VERIFIED.** `dev/ledger.toml:204`
understates the GCH closure as the brief notes (the closure is read from a
statement whose proof is not wired); I quote no figure from it and none is
needed for this verdict.

## 11. SECONDS, LOAD, RUNS (C-53, C-12)

One agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER
raised. Slot count (`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`)
run before EVERY invocation, all eight counts returned 0. **Floor:
`Floor349.agda`, an empty module, 0.066 s**, which confirms the target's floor
figure (0.07 s) and its machine note. All figures below are on this machine
and comparable within this task only.

| run | exit | seconds |
|---|---:|---:|
| `agents/tasks/LJ-1-349/Floor349.agda` (empty) | 0 | 0.066 |
| `agents/tasks/LJ-1-349/Refute349.agda` (scope slip, `∥_∥₁`) | 42 | 1.76 |
| `agents/tasks/LJ-1-349/Refute349.agda` (type slip, `Empty.rec`) | 42 | 1.12 |
| `agents/tasks/LJ-1-349/Refute349.agda` | **0** | **2.43** |
| `agents/tasks/LJ-1-349/Refute349.agda` (with `intended`) | **0** | **2.48** |
| `agents/tasks/LJ-1-348/Refute348.agda` (re-run, warm) | **0** | 1.08 |
| `agents/tasks/LJ-1-348/MustFail348.agda` (re-run, **EXPECTED RED**) | **42** | 1.47 |
| `agents/tasks/LJ-1-348/Field348.agda` (re-run) | **0** | 2.13 |

No invocation came near the 30-minute wall. No heap exhaustion. Nothing was
interrupted.

## 12. ARCHIVE USED (DD18)

One line per archived file, as the brief orders.

- **`agents/tasks/LJ-1-348/lj-1.348-report.md`, read WHOLE.** **Line read:**
  its section 3.2, 「the strongest true statement is the one I proved: no term
  inhabits `witK` at every `γ`, hence no supplier exists.」 **TOOK** the whole
  target as the object of review. **CORRECTED nothing in it; CONFIRMED its
  section 3.4 price basis and its extent table by re-measuring the counts.**
- **`agents/tasks/LJ-1-344/lj-1.344-report.md`, §6.1 and the answer table
  read.** **Line read:** `:186-188`, 「The easy countermodel is closed off:
  `shapedAt` forces every member of `w'` to be a shape, so `w'` cannot be the
  set that produces a membership cycle.」 **TOOK** the definition reading
  (correct) and the cure price. **REFUTED the inference** in section 5 of this
  report, at `file:line` as the brief demands.
- **`agents/tasks/LJ-1-345/lj-1.345-report.md`, §0-§2 read.** **Line read:**
  its §1.4, 「I wrote `agents/tasks/LJ-1-345/Refute345.agda`: the two
  pre-repair types transcribed from the commit diff, importing NOTHING from
  `LJ-1-341/`... The refutation no longer rests on the target's transcription
  at all.」 **TOOK** the standard and applied it: my `Refute349.agda` imports
  nothing from `LJ-1-348/`.
- **`archive/dev/TASKS-archived.md`, header `:1-20` read.** **Line read:**
  「The 264 rows below record every dispatch made on the retired route.」
  **TOOK SHAPE ONLY** (a dispatch history read for the practice of naming what
  a countermodel needs of its environment). **REJECTED every figure and every
  claim:** that route has a different carrier, a different coding and no
  `KFacts` record, so nothing in it prices anything here.

## 13. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `shapedAt` blocks the countermodel | **MEASURED FALSE.** Section 5, two countermodels plus delivered prose |
| `closedAt` speaks about tag 6 | **MEASURED FALSE.** Eight clauses read, section 1 |
| any of the twelve relations pins the arity slot | **MEASURED FALSE.** Twelve columns read, section 1 |
| the refutation rests on the target's transcription | **MEASURED FALSE.** My own file, exit 0 |
| the refuted premise is empty at the witness | **MEASURED FALSE.** Three layers, section 3 |
| the countermodel sits outside the chapter's premise class | **MEASURED FALSE.** `Live349.intended`, NEW |
| 「empty at every `γ`」 | **MEASURED FALSE** (and unclaimed by the target). Section 4 |
| `LeafAgree` has a consumer in `src/` | **MEASURED FALSE.** Ten hits read, named, section 3 |
| the cure is payable at `:6721` | **MEASURED FALSE.** Control re-run plus scope enumeration, section 6 |
| `KFacts` has a field for the carrier-in-the-bound | **MEASURED FALSE.** All 29 fields re-read and named by class |
| `graphWitK` is refuted | **MEASURED FALSE, it is INFERRED only.** Section 7; build before believing |
| anything landed in `src/` | **MEASURED FALSE.** `git status --short` shows only `agents/tasks/LJ-1-349/` files |
| a run hit a wall | **MEASURED FALSE.** Longest 2.48 s, section 11 |

## 14. WHAT I DID NOT SETTLE

- **`graphWitK`'s truth.** Still INFERRED false; section 7 says why it must be
  measured before it is believed.
- **The right restatement of the witness step.** Devlin's own (`w` fixed to
  the bound) versus the cheap hypothesis; the target's section 6 names both,
  and the choice is the orchestrator's (DD23).
- **The strengthening 「empty or vacuous at every environment」** priced at
  about 90 lines by the target. Not needed for this verdict after section 3's
  `intended` term, which already kills every use inside the premise class.

## 15. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-349/`: this report, `Refute349.agda`,
`Floor349.agda`. `MustFail348.agda` was re-run and NOT repaired. I read and
re-ran probes in `agents/tasks/LJ-1-348/`, `LJ-1-344/`, `LJ-1-341/`, `LJ-1-345/`
and edited none. I did not open `src/Everything.lagda.md`. No commit, no push,
no `git checkout`, `stash`, `reset` or `clean`. No `make check`. No em dash in
any language.
