# LJ-1.522 report: the definable powerset closure, from K being a limit level

**VERDICT: GO.** The obligation is written and it typechecks.
`agents/tasks/LJ-1-522/Probe522.agda:435-446`, exit 0, `runs/full-t2.out`.

    defPow-closed :
        (α : V ℓ) → IsLimit α
      → ∀ {n} (w K : Fin n) (γ : S ^ n)
      → fst (lookup K γ) ≡ Lset α
      → ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩
      → (z c v : S)
      → ⟨ fst c ∈ fst (lookup K γ) ⟩
      → ⟨ fst v ∈ fst (lookup K γ) ⟩
      → ⟨ (v ∷ c ∷ z ∷ γ) ⊨ DefBody w ⟩
      → ⟨ fst z ∈ fst (lookup K γ) ⟩

**W3 IS GO, ON THE SECOND RUN.** A limit level decomposes into the earlier
levels. `agents/tasks/LJ-1-522/runs/W3.agda:56-57`, exit 0, `runs/w3-1.out`.
The first run failed on one uninferred implicit and nothing else
(`runs/w3-0.out`).

**THE ONE SENTENCE FOR THE NEXT BRIEF.** The brief expected the limit to
discharge a definable powerset closure. **It does not have to.** The leaf's
third conjunct says `z` is a bounded SEPARATION of `w` with the recorded
satisfaction set `v` as its parameter (`src/L/Coding/Powerset.lagda.md:228-232`),
so the row costs a separation at a stage and not a relativization of an
arbitrary formula. **The environment's membership in `K` is what pays. The
code's membership is never consumed**, and
`agents/tasks/LJ-1-522/Probe522.agda:356-364` inhabits the same statement
without it.

## D-10, BEFORE ANY AGDA

The brief ordered this first. It changed the shape of the whole task.

### What the tree's notion of a limit level is

**The tower has NO limit constructor and NO limit predicate.**
`src/L/Constructible.lagda.md:16` states the design:

> equation covers zero, successors, and limits at once, and on von Neumann

The single recursion is `Lset α = ⋃ { 𝒟ₒ (Lset β) ∣ β ∈ α }`
(`src/L/Constructible.lagda.md:216`, `:222-223`), and its computation rule is
`Lset-compute` (`:227-228`). `isLayer` (`:175-181`) names the closure
principles of the tower and has five constructors, none of which is a limit.
So **a limit is a property of the INDEX and never of the stage**, and this
task has to say it. `Probe522.agda:72-75` says it:

    IsLimit α = IsOrd α × ⟨ ∅ ∈ α ⟩ × ((β : V ℓ) → ⟨ β ∈ α ⟩ → ⟨ sucV β ∈ α ⟩)

An ordinal, not zero, closed under the successor. **The tree has no other
reading available**, because the only vocabulary the ordinal chapter delivers
is `IsOrd` (`src/L/Ordinal.lagda.md:45`), `sucV` (`:56`) and `mem-ord`
(`:221`).

**NOT VACUOUS.** `ω` satisfies it, and the witness is in the file:
`Probe522.agda:116-121`, `ω-IsLimit`. A stop that rests on an empty
antecedent is not a stop, so the witness is written rather than argued.

### Whether `Lset` at a limit is the union of its predecessors

**YES, and it costs three lines.** This is W3 and it is section 1 of the
probe. `Lset-out` decomposes any member of `Lset α` as a member of
`𝒟ₒ (Lset δ)` for `δ ∈ α` (`src/L/Constructible.lagda.md:336-338`).
`Lset-suc` identifies that definable powerset with the NEXT stage
(`src/L/Axioms/Basic.lagda.md:196`). The successor closure of a limit puts
that next index back inside `α`. So

    limit-union : (α : V ℓ) → IsLimit α → (x : V ℓ) → ⟨ x ∈ Lset α ⟩
                → ∥ Σ[ δ ∈ V ℓ ] (IsOrd δ × ⟨ δ ∈ α ⟩ × ⟨ x ∈ Lset δ ⟩) ∥₁

`Probe522.agda:77-90`, and alone in `runs/W3.agda:56-66`.

**The D-10 stop the brief prepared does not fire.** The cure `[LJ-1.520]`
named is available in this tree.

### The third thing D-10 found, and it corrects the brief's price

The brief prices the row as a definable powerset closure: "`K` must already
hold every definable subset of every member of `K`". **Read as a statement
about `𝒟ₒ w` for an arbitrary `w ∈ K`, that is a chapter and not a probe.**
It needs the definable subsets of `w` to be relativized to a stage above `w`,
and the tree's `relativize` (`src/FOL/Manipulation/Relativize.lagda.md:48-60`)
tightens unbounded quantifiers only; it does not tighten the bounded ones, so
it does not bridge the inner satisfaction of `DefOf w` to the ambient reading
for a `w` that is not transitive. `archive/dev/LJ-dispatch-index.md:268`
already measured a neighbour of this and called it a chapter.

**The brief's own words save it.** The statement it names is "every definable
subset of a member of `K`, **with a code and an environment in `K`**". With
the environment `v` in hand the subset is not an arbitrary definable subset.
It is the set `{ u ∈ w : envOne u ∈ v }`, which is what the leaf's third
conjunct says (`src/L/Coding/Powerset.lagda.md:228-232`,
`DefinesAt-out`/`DefinesAt-in` at `:254-264`). **That is a Δ₀ separation with
two parameters, and the tree already carves those at a stage**
(`src/L/Axioms/Separation.lagda.md:273-320`).

So the row is paid at the price of a separation. **I did not build the
definable powerset closure and I do not claim it.** What I claim is the
statement the brief wrote.

## WHAT THE PROBE BUILDS, AND WHERE EACH PIECE CAME FROM

| section | what | at |
|---|---|---|
| 1 | `IsLimit`, `limit-union`, `ω-IsLimit`, `twoBelow`, `closeAt` | `Probe522.agda:72-130` |
| 2 | the one-entry environment as a Δ₀ formula, both directions | `:150-256` |
| 3 | separation at a stage, with the stage EXPOSED | `:258-317` |
| 4 | the separating formula and the obligation | `:320-446` |

**SECTION 2 IS THE ONE PLACE NEW SYNTAX WAS NEEDED, AND IT IS SIX LINES.**
The tree already carries the Kuratowski pair of the empty set as a Δ₀ reader
over the hierarchy: `tag0At` (`src/L/Coding/Environment.lagda.md:336-339`),
its Δ₀ witness (`:348-351`) and its adequacy (`:452-455`). `liftFo` carries a
constant-free Δ₀ reader into the object language of `L`
(`src/L/Absoluteness.lagda.md:90-92`) and `transferFo` says the two agree
(`:122-127`). A one-entry environment is the SINGLETON of one such pair
(`src/L/Coding/Environment.lagda.md:84-86`), and "singleton" is two bounded
quantifiers over the set itself:

    envOneL e x = ∀̇∈ (var e) (tag0AtL zero (suc x)) ∧̇ ∃̇∈ (var e) ⊤̇

`Probe522.agda:189-190`. **No bound `K` occurs in it and no constant occurs in
it.** That is the property that lets the formula travel to a STAGE. The
delivered `envOneBndS` (`src/L/Condensation.lagda.md:1766-1769`) says the same
thing but takes `K` as a slot, and a formula bounded by `K` cannot be carved
inside a level of `K`.

**SECTION 3 IS A COPY AND IT IS DECLARED AS ONE.**
`src/L/Axioms/Separation.lagda.md:273-320` already carves a Δ₀ subset of a
member of a stage, but it returns `isContr (SetOf …)` and spends the stage
inside. This task needs the stage, because the whole discharge is "the carved
set lands one stage up, and one stage up is still below the limit". So the
same body is rerun at `Probe522.agda:266-317` with `carve ψ` and
`carve∈𝒟ₒ ψ` as the return value. Nothing else changes. **If this ever lands
in `src/`, the right move is to widen `separateAt` rather than to keep the
copy.**

**SECTION 4 SPENDS THE LINEAR ORDER ONCE.** `twoBelow`
(`Probe522.agda:92-114`) puts the carrier `w` and the environment `v` inside
ONE earlier level, and it needs `ord-tri` (`src/L/Ordinal/Linear.lagda.md:136`)
to choose the larger of the two levels `limit-union` returns. **That is the
only classical step this file adds**, and it is the only use of `lem` that is
not already inside an import.

## WHAT THE STATEMENT COSTS, AND WHAT IT DOES NOT

**IT DOES NOT NEED THE CODE.** `defPow-closed-noCode`
(`Probe522.agda:356-364`) is the same statement with `⟨ fst c ∈ fst (lookup K γ) ⟩`
removed, and it carries the whole proof. `defPow-closed`
(`:435-446`) is one line: it forgets the extra argument. **So the brief's
statement is weaker than what the limit actually gives.** The next brief may
state the row without the code.

**IT DOES NOT NEED `K` TO BE TRANSITIVE.** `transK` is not a hypothesis here.
The carrier `w` may be any member of `K`, and no member of `w` is asked to lie
in `K`.

**IT DOES NEED `K` TO BE A LEVEL AND NOT MERELY A SET.** The hypothesis is
`fst (lookup K γ) ≡ Lset α`. A `K` that is an elementary submodel of a level,
which is what the condensation argument finally applies this to, does NOT
satisfy it. **That is the gap this task leaves and the next brief has to
price**: either the condensation `K` is a level at the point where `leafB` is
converted, or the row has to be re-derived at the collapse.

**IT DOES NEED THE ENVIRONMENT IN `K`.** That is the whole load. Without it
the subset is defined by a formula whose parameters are outside every level
below `α`, and no separation at a level below `α` reaches it.

## WHAT THE GRADED FORMULA OWES AFTER THIS

`[LJ-1.520]`'s nine-row table (`agents/tasks/LJ-1-520/lj-1.520-report.md:237-245`),
re-walked, with this task's row marked.

| hypothesis | status after this task |
|---|---|
| the twelve tag slots hold the numerals 0 to 11 | NO LONGER NEEDED (`pins`) |
| the two term tags hold 0 and 1 | NO LONGER NEEDED (`pins`) |
| the numerals lie in `K` | **UNDELIVERED.** A hypothesis on `K` |
| `K` is closed under pairing | **UNDELIVERED.** A hypothesis on `K` |
| the codes and recorded values of a shaped code lie in `K` | **UNDELIVERED.** A hypothesis on `K` |
| the environment sets and their members lie in `K` | **UNDELIVERED.** A hypothesis on `K` |
| the term values lie in `K` | **UNDELIVERED.** A hypothesis on `K` |
| a satisfier reached through a member of `K` lies in `K` | SAID by `transK` |
| **`K` is closed under the definable powerset of its members** | **PAID BY THIS TASK**, `Probe522.agda:435` |

**THE FIVE ARE STATED AT THIS TASK'S FRAME, AND ALL FIVE ARE UNDELIVERED.**
The brief asked me to check both halves and they answer differently.

- **Stated at the same frame: YES.** `[LJ-1.520]` cites
  `src/L/Condensation.lagda.md:4413-4457`, the parameter telescope of
  `MemAgree` (`:4412`). Every row there reads `⟨ fst a ∈ fst (lookup K γ) ⟩`,
  for example `numK` at `:4414` and `pairK` at `:4417-4418`. **`K` is a value
  read out of an environment, exactly as in `defPow-closed`.** So the ninth row
  and the five sit in one telescope shape and no re-framing is owed.
- **Delivered: NO, none of the five.** `MemAgree`'s telescope is fed from a
  record. `LowerAgree` (`src/L/Condensation/LowerAgree.lagda.md:228-231`) takes
  `lf : LFacts …` as a MODULE PARAMETER and passes the fields straight through
  at `:255-259`. `TwelveAgree` builds that record from its own frame at
  `src/L/Condensation/TwelveAgree.lagda.md:405-435`, and the frame is
  `AbstractFrame` (`:337-343`), which takes `tf : TFacts …` as a module
  parameter. `TFacts` is declared at `:129` and its fields are the five rows,
  for example `pairK` at `:159` and `valV` at `:244`. **`grep -rn "TFacts" src`
  returns three lines and all three are inside `TwelveAgree`**: the
  declaration, the parameter and the `open`. **Nothing in `src/` constructs a
  `TFacts`, so nothing in `src/` discharges any of the five.**

**SO THE ROW COUNT AFTER THIS TASK IS: two retired, one said, one paid, five
open.** The five are open in the same way they were before, and this task did
not change them.

**ONE OF THE FIVE MAY NOW BE CHEAP AND I DID NOT MEASURE IT.** "The numerals
lie in `K`" at `K = Lset α` for a limit `α` should follow from the numerals
being constructible at finite stages, but I did not write it and I do not
claim it. **It is the natural next probe** and it is smaller than this one.

## THE UNCONSUMED CERTIFICATE

`[LJ-1.520]` reports a delivered `Σ₁` certificate at
`src/L/BoundedSubset.lagda.md:145-146` (`Σ₁-levelHood`) and a second at
`:858-859` (`Σ₁-Σ₂`), both unconsumed.

**I DID NOT CONSUME EITHER, AND THE PROBE DOES NOT IMPORT
`L.BoundedSubset`.** `Probe522.agda:16-55` is the whole import list and the
module is not in it.

**WHAT CONSUMES IT AFTER THIS TASK: NOTHING YET, AND I NAME NO CONSUMER.**
Re-measured today, `grep -rn "Σ₁-levelHood\|Σ₁-Σ₂" src` returns four lines and
all four are the declarations themselves
(`src/L/BoundedSubset.lagda.md:145`, `:146`, `:858`, `:859`). Every other hit
in the tree is in `agents/tasks/archive/`, that is, in retired probes
(`agents/tasks/archive/LJ-1-50/ProbeDD25H5.agda:98`,
`agents/tasks/archive/LJ-1-50/ProbeDD25H8.agda:83`). **`[LJ-1.228]`'s record
still holds** (`agents/tasks/LJ-1-228/lj-1.228-report.md:33-36`).

**What this task changes about it is only this:** the transport that would
consume the certificate needs the leaf conversion, the leaf conversion needs
this row, and this row is now paid at a level carrier. So the certificate's
consumer is one step nearer, and it is still not written.

## THE PRICE

Three forced rechecks each. The interface was removed before every run, so
each number is a real recheck of the file and not a cache hit.
`GHCRTS="-A64m -I0 -M8g"`, the wide caliber, set on the pane by the program
and untouched.

| file | median wall | peak RSS | runs |
|---|---|---|---|
| `runs/W3.agda` alone | **1.19 s** | **282,918,912 B** | `runs/w3-t1.time`, `w3-t2.time`, `w3-t3.time` |
| `Probe522.agda`, full | **3.25 s** | **463,601,664 B** | `runs/full-t1.time`, `full-t2.time`, `full-t3.time` |

All six exited 0.

**SIZE.** `Probe522.agda` is 446 lines, of which 312 are non-blank and not a
comment. `runs/W3.agda` is 66 lines, of which 31 are non-blank and not a
comment.

**AGAINST THE BRIEF'S ESTIMATE, WHICH WAS LOW, AND IT SAID SO.**

| item | brief | measured |
|---|---|---|
| W3 | about 25 lines, under 40 s | 31 lines, 1.19 s |
| the probe | about 160 lines | 312 lines |
| the obligation | about 45 lines | 91 lines (`:356-446`) |

**W3 came in on the line estimate and far under the time estimate.** The
probe came in at 1.95x the line estimate. **The overrun is entirely sections 2
and 3**, which the brief did not price because it priced the row as a closure
rather than as a separation. Section 2 is 107 lines and section 3 is 60. The
brief warned its own estimate might be low and it was.

**NO WALL EVENT.** No heap exhaustion, no rerun after a wall, one Agda process
per run.

## W2, ANSWERED

**W2 is met and it cost nothing to meet.** Every piece of section 2 and
section 3 is written at a generic arity `∀ {n}` with generic slots
(`Probe522.agda:150`, `:165`, `:172`, `:189`, `:192`, `:195`, `:226`), and the
obligation instantiates them. Nothing is written at a fixed arity and nothing
mentions a stage in the generic part. The one carrier-specific object is
`envInAt` (`:320`), which is at arity one because `AtStage.carve` carves with
a one-variable formula (`src/L/Axioms/Separation.lagda.md:291-292`), and that
is the tree's shape and not this task's choice.

**W4, ANSWERED: NOTHING IS RETIRED BY THIS TASK.** It lands nothing in `src/`
and it removes no module. The one duplication it creates is section 3, and
that duplication is declared above with the repair named.

## WHAT I DID NOT DO

- **I did not put the closure in a formula.** It is a frame hypothesis on a
  value. `[LJ-1.520]`'s circularity finding
  (`agents/tasks/LJ-1-520/lj-1.520-report.md:262`) is not touched and not
  tested.
- **I did not rebuild the graded formula or the transport.**
  `Probe522.agda:16-55` imports neither `L.BoundedSubset` nor
  `L.Condensation`.
- **I did not assume `[LJ-1.519]`'s reading of the limit.** I read the tower
  in `src/L/Constructible.lagda.md` and wrote the reading the tower supports.
  The reading agrees with the source's union law, which is a fact about the
  source and not an input to this file. See `## LITERATURE USED`.
- **I did not postulate.** The file carries `--safe`
  (`Probe522.agda:1`).
- **I did not commit and I did not push.** The working tree holds
  `agents/tasks/LJ-1-522/` and nothing else.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ, AND IT CHANGED THE PRICE.**
  `archive/dev/LJ-dispatch-index.md:268`:

  > | LJ-1.196 | DefAt's ambient reading: 84 lines or a chapter | NO-GO: IT IS A CHAPTER | u's slot is d, the definable powerset of the recorded value, and the induction never pins it |

  This is the neighbour of the reading the brief asked for, and it is already
  measured as a chapter. It is why I read the leaf as a separation instead.
  Also `:243`:

  > | LJ-1.167 | The definable power at a general argument, and pairing at a general limit | GAP 2 GO AT 35, GAP 1 NO-GO | Gap 2 sat in the prior dispatch's file. Devlin leaves gap 1 as an exercise |

- **`archive/dev/JOURNAL.md`: READ.** `archive/dev/JOURNAL.md:807`:

  > `u`'s slot is the definable powerset of the recorded value and the induction

  The same finding in prose. It confirms the index row above and adds nothing
  this task needed.

- **`archive/dev/JOURNAL-archived.md`: READ, ONE LINE, AND IT DID NOT APPLY.**
  `archive/dev/JOURNAL-archived.md:3928`:

  >   on the warrant that `[L3.19]` reads the definable powerset off it; three

  That is the `L3` route and this task is on `LJ-1`. Not used.

- **`dev/ARCHIVE.md`: READ, AND DECLINED FOR THIS TASK.** Its rows are
  retirement records for `L.Rud.*` and `L.Godel.Definable` and one partial cut
  of `L.Condensation` (`dev/ARCHIVE.md:285`). None of them names the leaf's
  third conjunct, the one-entry environment or a limit level. **Nothing to
  revive here.**

- **`archive/dev/ORCHESTRATION.md`: NOT USED.** It is the archived operating
  document for the pre-program loop. The program is the operating document now
  and the probe rules I followed are in
  `dev/pod/instructions/coder.md` and `AGENTS.md`. Declined.

## LITERATURE USED

- **`dev/literature/devlin-II5.md`: READ, ONE LINE, AS A CHECK AND NOT AS AN
  INPUT.** `dev/literature/devlin-II5.md:238`:

  > 6. The union law L_β = ⋃_{γ<β} L_γ at limit β (`dev2.txt:1298-1301`).

  **The tree's reading agrees with the source's union law.** I read the tree
  first and wrote `limit-union` from `Lset-out` and `Lset-suc`; this line is
  the after-the-fact check that the reading is the standard one. The brief
  forbids assuming `[LJ-1.519]`'s reading and I did not: the Agda depends on
  `src/L/Constructible.lagda.md` and `src/L/Axioms/Basic.lagda.md` only.

- **`dev/literature/level-formula-slot-roles.md`: READ, ONE ROW, AND IT
  SUPPORTS THE FRAME CHOICE.** `dev/literature/level-formula-slot-roles.md:29`:

  > | 7 | Jech 13.13 | A Π₂ SENTENCE `σ`: `(M,∈) ⊨ σ` iff `M = L_δ` for a limit `δ` | **0** | everything | nothing | level-hood is a property of the CARRIER | `_build/literature/jech13.txt:605-614` |

  "Level-hood is a property of the CARRIER" is the same conclusion this task
  reaches from the other side: the closure is a fact about the carrier value
  and cannot be a conjunct of the matrix.

- **`dev/literature/digest.md`: NOT READ.** It is the cross-source digest and
  the two files above answered the only two questions this task put to the
  literature. Declined.

- **`dev/literature/geology.md`: NOT READ.** Set-theoretic geology is not on
  this task's path. Declined.

- **`dev/literature/terms-2026-08.md`: NOT READ.** It is the terminology
  dossier. This task adds no term to `dev/glossary.toml` and names no new
  concept in Chinese or Japanese. Declined.

## FOR THE NEXT BRIEF

1. **State the row without the code.** `defPow-closed-noCode` is the honest
   type and the code hypothesis is dead weight.
2. **Price "the numerals lie in `K`" at `K = Lset α`, `α` a limit.** It is the
   cheapest of the five open rows and it may fall to the same limit.
3. **Settle whether the condensation `K` is a level where `leafB` is
   converted.** This task pays the row only for a level. If the conversion
   happens at the submodel and not at the level, the row has to be re-derived
   through the collapse, and that is a different task with a different price.
4. **If any of this lands in `src/`, widen `separateAt` instead of copying
   it.** Section 3 is a copy and it should not survive as one.
