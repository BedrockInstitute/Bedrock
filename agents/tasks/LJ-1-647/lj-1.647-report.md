# LJ-1.647 report: the hull is closed under Lset, from the keystone

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.647
obligation: agents/tasks/LJ-1-647/Probe647.agda::hull-closed-lset
verdict: **GO on the obligation, and the brief's premise 2 is REFUTED.**
The obligation is green and metered (`runs/meter-obligation.out`,
`pass exit=0 2.94 s`, `0 UNRESOLVED of 1`, `probe_red=False`).
**READ THIS BEFORE YOU QUEUE ANYTHING: the term carries `[LJ-1.646]`'s
keystone as a NAMED HYPOTHESIS and that supplier is not built. So step 2
is REDUCED to the keystone. It is not PROVED.**

**WHAT THE TASK EARNS, IN ONE SENTENCE.** Step 2 costs TEN LINES and no
formula at all (`Probe647.agda:135-149`), because the hull IS the image
of `Code` under `val` by its own definition
(`Hull = sett Code (λ c → toSet (val c))`, src/L/Hull.lagda.md:114-115),
so a hypothesis that PRODUCES a code discharges closure directly and
`hull-closed` is never reached.

**AND THE KEYSTONE MAY BE TRUNCATED.** `[LJ-1.646]` does not have to
choose the code. `hull-closed-lset∥` (`Probe647.agda:171-173`) closes
step 2 from `∥ Σ[ d ∈ Code ] ... ∥₁`, and it is the SAME proof: the
untruncated form is its corollary (`:155-156`). This is measured, not
argued, and it removes a whole class of failure from 646's brief.

Written as a skeleton before any Agda beyond the floor and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-647/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at a
time. I did not set `GHCRTS`. Nothing is postulated, the probe carries
`--safe`, the delivered probe is green and carries no hole, and nothing
lands in `src/`. The probe is a raw `.agda` file, so it carries no
` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot fire
on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any
run is 512,917,504 bytes against the 2,147,483,648-byte wide cap, 24 % of
it, and that run is `runs/p-final.out`, the delivered bytes. The longest
Agda run is 3.74 s (`runs/p-5.out`) against the caps I set (600 s for the
floor and W3, 900 s for the probe). The caps are wall-clock caps
enforced by a perl alarm (`runs/run.sh` carries the mechanism), because
this macOS has no `timeout` ([LJ-1.602], [LJ-1.610]).

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE**
(708 `.agdai` files under `_build/` at the start of the task). No number
here is a cold-cache number, and this report does not bound one.

## THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

**`[LJ-1.646]` HAS NO TASK HOME AND NO REPORT, AND THAT IS BY DESIGN, NOT
A DEFECT.** `agents/tasks/LJ-1-646/` does not exist and
`agents/tasks/LJ-1-646/LJ-1.646.md` is unwritten; 646 is a SIBLING queued
in the same block as this task, not a predecessor. The mathematician says
so in the queue: "Four consumers take the keystone as a hypothesis, so
backlog item 27 does not bite: nothing reads a RUNNING sibling's output"
(`dev/pod/queue.toml:6216-6217`).

So the standing coder clause "a module hypothesis taken from a
predecessor is the type that predecessor delivered" has no predecessor to
read here, and I did not invent one. **I took the hypothesis type from
the tree instead**, verbatim from `[LJ-1.462]`'s own D-10 correction
(`agents/tasks/LJ-1-462/Probe462.agda:118-121`), which is the same file
and the same lines the queue block cites as the keystone's source
(`dev/pod/queue.toml:6207`). The type is restated at `Probe647.agda:103-107`.
If 646 lands a DIFFERENT type, read "WHAT THE NEXT BRIEF NEEDS" below:
this task measured which variations still close step 2 and which do not.

## THE FLOOR, BEFORE ANY PROOF

The standing coder clause orders a floor before the proof. The floor slice
is `runs/FLOOR.agda.txt`: the trimmed frame, both types in full, and a HOLE
where the term goes. Its run is `runs/floor-1.out`: **exit 42 at 2.81 s,
peak 415,465,472 bytes**, with `[UnsolvedInteractionMetas]` at the one
designed hole and no other error.

**THE FRAME IS CHEAP HERE AND THE TRIM IS WHY.** The clause also orders
the imports trimmed to the facts my own rows use. Step 2's statement names
`Code`, `val`, `Lset`, `IsOrd` and hull membership, and NOTHING ELSE, so I
dropped everything `[LJ-1.462]` imported for `feed`: `L.Coding.Sequence`
(`LsetGraph`, `LsetGraphAt`), `FOL.Syntax`, `FOL.Manipulation.Parameters`
(`absFo`, `countFo`), `V.Collapse` and its `module C = Collapse M`,
`L.Constructible.𝒮ʟ`, `Cubical.Data.Nat` and `Cubical.Data.Vec`. Compare
`agents/tasks/LJ-1-462/Probe462.agda:24-40`. **The floor costs 0.39 GiB
against a 2 GiB cap and the finished probe costs 0.48 GiB, so this frame
has about 4x headroom under the WIDE tier and never needed the heavy
one.**

**THE SLICE IS DELIVERED WITH A `.txt` SUFFIX, ON PURPOSE.** It is red by
design, and every `.agda` under a task's own directory is a verification
target of the acceptance run (`scripts/pod/facts.py:489`,
`verification_target`), so a red slice left as `.agda` would fail conjunct
1 and would report this task's landed obligation as a NO-GO. The bytes are
what produced `runs/floor-1.out`, and the file's own header carries the two
commands that reproduce the run.

## W3, AND ITS ESTIMATE IS REFUTED DOWNWARD

**The brief names W3 as "the `Formula Code 1` that `hull-closed` needs,
built from the keystone's `d`", at 70 to 150 lines. THE ANSWER IS ZERO
LINES, because `hull-closed` is not on the route.**

`runs/W3.agda` is the decisive miniature and `runs/w3-1.out` is its first
run: **exit 0 at 2.82 s, peak 469,942,272 bytes**, re-run green at
`runs/w3-final.out` (exit 0, 2.44 s). It builds the whole obligation with
no `Formula` anywhere and no import of `FOL.Syntax` at all.

**GO, and the price is 10 lines, not 70 to 150.**

## THE OBLIGATION, AND WHAT ITS TYPE SAYS

`hull-closed-lset` at the top level (`Probe647.agda:206-214`), which is
where `witness = Target.<dotted-name>` reads it (`scripts/pod/witness.py:278`):

    hull-closed-lset : (lam : S) (ordλ : IsOrd lam)
      (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
      (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
      (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
      → HullStage.LsetCodeOrd lam ordλ succλ X X⊆L ∅∈λ
      → (y : S) → ⟨ y ∈ˢ HullStage.M lam ordλ succλ X X⊆L ∅∈λ ⟩ → IsOrd y
      → ⟨ Lset y ∈ˢ HullStage.M lam ordλ succλ X X⊆L ∅∈λ ⟩

The telescope is `[LJ-1.462]`'s `HullStage` (`Probe462.agda:78-88`) minus
`module C = Collapse M`. **`succλ` is unused by this obligation and I KEPT
it**, because the consumer site carries it and `[LJ-1.649]` must be able to
lift these terms verbatim.

**THE HYPOTHESIS IS NAMED AND UNPAID.** `LsetCodeOrd` (`:103-107`) is
`[LJ-1.646]`'s obligation and I did not build it. **If `LsetCodeOrd` is
uninhabited, everything here is vacuous.** 646 decides that and this task
says nothing about it.

## THE STRUCTURAL FACT, PINNED BY `refl`

    hull-mem-is-code : (x : S)
                     → ⟨ x ∈ˢ M ⟩ ≡ ∥ Σ[ c ∈ Code ] (fst (val c) ≡ x) ∥₁
    hull-mem-is-code x = refl                    -- Probe647.agda:89-91

**To be in the hull IS to be the value of a code, DEFINITIONALLY.** The
tree already said it twice and neither line was a proof: `Hull` is built as
the image set, `Hull = sett Code (λ c → toSet (val c))`
(src/L/Hull.lagda.md:114-115), and the reader back is the identity,
`hull-member x x∈H = x∈H` (src/L/Hull.lagda.md:339). `inHull c = ∣ c , refl ∣₁`
(:118) is the other half. This one `refl` is the whole task.

## WHAT THE BRIEF GOT WRONG

**PREMISE 2 IS FALSE AS STATED.** It reads: "`hull-closed` is the hull's
ONLY closure rule and it takes a `Formula Code 1`, so any closure demand
needs the condition NAMED in the hull's language. Basis:
src/L/Hull.lagda.md:415". The cited line is real and `hull-closed` is at
:415. **But it is not the only closure rule.** `val-in-Hull c = inHull c`
(src/L/Hull.lagda.md:341-342) is a constructor-level rule with no formula
in it, and it is the one this task used.

**WHAT `hull-closed` ACTUALLY BUYS is an EXISTENTIAL SEARCH**, and that is
the distinction premise 2 missed. Given a formula satisfied by SOMETHING,
`hull-closed` finds a hull member satisfying it: its hypothesis is
`⟨ [] AbsL.⊨ᵐ (∃̇ (mapFo val φ)) ⟩` and it returns a truncated Σ. **You
need it exactly when you do NOT have the code.** `[LJ-1.646]` hands the
code over, so the search is already done and the formula has nothing left
to do.

**PREMISE 3 IS RIGHT IN ITS CONCLUSION AND WRONG IN ITS REASON.** It says
naming `Lset` in the hull's language is 646's obligation, and that is
correct: 646 must still build a `Formula (⊥*) (suc k)` inside `wit` to
make the code exist. But the naming is needed to BUILD THE CODE, not to
feed a `Formula Code 1` to `hull-closed`. **The consumer never sees a
formula.** That distinction is what makes step 2 a ten-line corollary
instead of a 70-to-150-line build.

**PREMISE 4 IS CORRECT AND THIS TASK EXPLAINS IT.** `[LJ-1.479]` and
`[LJ-1.481]` both closed NO-GO, and both stopped at the same sentence:
"`IsOrd` has no source at a hull member" (`lj-1.481-report.md:80`,
`lj-1.479-report.md:85`). Both went down the `wit`-then-`inHull` route
through UNIQUENESS, via `Lset-only` and a term they both called `pins`.
**TWO hypotheses moved since, not one, and the report should say both.**
(a) The brief ADDS `IsOrd y`, so this task does not have to FIND the
ordinality 479 and 481 could not find; it is handed over and passed
straight to the keystone. (b) The keystone replaces uniqueness entirely.
**Neither alone would have been enough**, and a brief that credits only
the keystone will mis-price the next three.

## WHY UNIQUENESS WAS THE WRONG QUESTION, AND IT IS A LITERATURE FINDING

Devlin's hull is defined BY UNIQUE DEFINABILITY: "a ∈ M iff for some
formula φ(v₀) of ℒ_X, a is the unique element of L_α such that L_α ⊨ φ(a)"
(dev/literature/devlin-II5.md:122-123, quoting `dev2.txt:1331-1333`).
**Bedrock's hull is not that hull.** `search` takes the LEAST witness under
a well-order, `leastOf wo` (src/L/Hull.lagda.md:81), and membership is
indexed by `Code` rather than by a formula that pins its value. The
re-indexing has a date and a task: "`[LJ-1.23]` re-indexed the hull by
`Code`" (archive/dev/JOURNAL.md:328).

**So `[LJ-1.479]` and `[LJ-1.481]` were priced against the textbook's hull
and not against the tree's.** They needed uniqueness because Devlin's
definition needs it. The tree's definition never did. Neither report was
wrong about its own route; both were measuring a route the carrier had
already made unnecessary, and nobody noticed for 166 dispatches.

This is C-42 in shape but NOT a refutation, so I did not run the sweep: I
refuted a PREMISE OF THIS BRIEF, not a statement in the tree. If the
mathematician reads the finding as a refutation of the uniqueness route
wherever it appears, the sweep is theirs to order and its search key is
`pins` plus `Lset-only`.

## W2 (DD4)

**The mathematics is written ONCE, at a generic operation, from the
WEAKEST hypothesis, and everything else in the file is an instance.**
`hull-closed-op∥` (`Probe647.agda:135-149`) is the only proof: it is
generic in the operation `F : S → S`, generic in the side condition
`P : S → Type (ℓ-suc ℓ)`, and takes the code map TRUNCATED. Nothing in its
body mentions `Lset`, `IsOrd`, or any stage.

The four other terms are corollaries and cost one line each:

- `hull-closed-op` (`:155-156`), the chosen form, from `∣_∣₁`.
- `hull-closed-lset` (`:165-167`), THE OBLIGATION, at `F = Lset`, `P = IsOrd`.
- `hull-closed-lset∥` (`:171-173`), the same from the truncated keystone.
- `hull-closed-lset-plain` (`:187-189`), at `P = Unit*`, which is
  `[LJ-1.462]`'s step 2 with nothing added.

**`[LJ-1.648]` and `[LJ-1.650]` should take `hull-closed-op∥` and supply
their own `F`.** The clause's conflict did not arise: generic was cheaper
here on the FIRST instance, not merely from the second, because the
generic statement is what showed the formula was unnecessary.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`. No dead fragment was
deleted. `dev/ARCHIVE.md` gains no row from this task.

## WHAT THE NEXT BRIEF NEEDS

**FOR `[LJ-1.646]`, THE KEYSTONE ITSELF.** Its brief can be relaxed in one
place and must not be relaxed in another.

1. **It may return TRUNCATED existence.** `∥ Σ[ d ∈ Code ] (fst (val d) ≡
   Lset (fst (val c))) ∥₁` closes step 2 exactly as well as the chosen
   form: `hull-closed-lset∥` (`Probe647.agda:171-173`), green in
   `runs/p-final.out`. The second truncation is free because the goal is
   itself an hProp. **Do not spend a dispatch choosing the code.**
2. **The equality must be at `fst (val d)`, in `S`.** An equality at `SL`
   would need `cong fst` and still works; an equality only up to the
   hull's own membership would NOT, because the subst at `:143-145` needs
   a path in `S`.
3. **`IsOrd (fst (val c))` as the side condition is fine and is not the
   only option.** `hull-closed-op∥` takes ANY `P`, so if 646 finds it
   needs a different or extra hypothesis on `c`, step 2 absorbs it with no
   new proof, provided every consumer can supply it.

**FOR `[LJ-1.649]`, THE COMPOSITION.** `hull-closed-lset-at-ord`
(`:194-196`) is step 2 in the argument order `levelIn` will want,
`(y : S) → IsOrd y → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩`. The telescope matches
`[LJ-1.462]`'s `HullStage` exactly, `succλ` included, so the term lifts
verbatim. **Step 2 is no longer a cost in 649's price; treat it as free
given the keystone.**

**FOR `[LJ-1.648]` AND `[LJ-1.650]`.** Ask FIRST whether the obligation
needs a formula at all, before pricing one. The question to ask at each
site is: do I have a CODE, or only a CONDITION? If a code, use
`hull-closed-op∥`. If only a condition, `hull-closed` is the right rule
and its price is real. **`[LJ-1.641]`'s premise, that all three of clause
(iii)'s gaps have one producer, is untouched by this task and I did not
test it.**

**WHAT THIS TASK DOES NOT SETTLE.** It does not build `lset-code-ord`. It
does not inhabit `levelIn`. It does not touch step 3 or step 4. It does not
produce `IsOrd` at a hull member, which is what `[LJ-1.479]` and
`[LJ-1.481]` actually wanted, and that statement is still unbuilt and still
unrefuted. It does not touch `cover`. It does not edit `src/`. It does not
run C-42's sweep.

## RUNS, AND ONE HARNESS ARTIFACT WORTH RECORDING

All runs under `GHCRTS=[-A64m -I0 -M2g]`, one Agda process at a time.

| run | file | exit | seconds | peak bytes |
|---|---|---|---|---|
| `runs/floor-1.out` | `FLOOR.agda.txt` | 42 (designed hole) | 2.81 | 415,465,472 |
| `runs/w3-1.out` | `W3.agda` | 0 | 2.82 | 469,942,272 |
| `runs/w3-final.out` | `W3.agda` | 0 | 2.44 | 434,159,616 |
| `runs/p-1.out` | `Probe647.agda` | 42 (`Unit*` not in scope) | 2.70 | 451,264,512 |
| `runs/p-2.out` | `Probe647.agda` | 0 | 3.49 | 352,600,064 |
| `runs/p-3.out` | `Probe647.agda` | 1 (HARNESS, not Agda) | 0.08 | 4,980,736 |
| `runs/p-4.out` | `Probe647.agda` | 0 | 3.36 | 365,805,568 |
| `runs/p-5.out` | `Probe647.agda` | 0 | 3.74 | 343,425,024 |
| `runs/p-final.out` | `Probe647.agda` | 0 | 2.71 | 512,917,504 |

Meters, all against the delivered bytes:

- The obligation: `0 UNRESOLVED of 1`, 2.94 s, `probe_red=False`
  (`runs/meter-obligation.out`).
- All eight delivered names in one grouped run: `0 UNRESOLVED of 8`,
  2.34 s, `probe_red=False` (`runs/meter-names.out`).
- This worktree has no `.venv`. The meter ran as
  `/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`. I
  did not add a dependency and I did not create a local `.venv`.

**TWO NON-AGDA FAILURES HAPPENED AND I AM RECORDING THEM RATHER THAN
HIDING THEM.** `runs/p-3.out` exited 1 in 0.08 s with `time: command
terminated abnormally / time: signal: Invalid argument`: the perl-alarm
wrapper failed to exec, so **no Agda process started**. `runs/witness.out`
and `runs/witness-2.out` are the witness meter returning `probe-red
exit=-9` at 1.59 s and 1.70 s, a SIGKILL, on a probe that was already
green. **Neither is an Agda result and neither is evidence about the
term.** I confirmed that by running the meter's own generated witness file
by hand, `.pod-state/witness/Witness-POD-7ea91ed8.agda`, which returned
EXIT=0 at 2.61 s; the meter then passed on every subsequent run. Both
files are kept because they are evidence and evidence is never deleted.
**This machine is `shared` and other Agda processes were live during the
task**, which is the likeliest cause and which I did not prove. **If a
future task sees `exit=-9` from `witness.py` on a green probe, re-run it
before believing it.**

## ARCHIVE USED

- **`archive/dev/JOURNAL.md`. READ, AND IT SUPPLIED THE FINDING.**
  Quote at `archive/dev/JOURNAL.md:328`:

  > **DD27 landed.** `[LJ-1.23]` re-indexed the hull by `Code`, 372 to 431 lines at

  This is the provenance of the exact fact this task turns on. The hull
  became code-indexed at `[LJ-1.23]`, which is why `hull-mem-is-code` is
  `refl` and why the uniqueness route `[LJ-1.479]` and `[LJ-1.481]` took
  was already unnecessary when they took it.

- **`archive/dev/JOURNAL-archived.md`. READ, and it is a contrast I did
  not transfer.** Quote at `archive/dev/JOURNAL-archived.md:1646`:

  > ANY LEVEL WITH A NONTRIVIAL ORDER.** The batch's own question is answered no: the hull's two

  The passage names an expressibility obstruction: a general-level formula
  needing internalized satisfaction that the campaign retired. **My route
  meets no formula, so that obstruction does not arise here.** I did not
  transfer the finding by analogy in either direction; it describes a
  retired route and I record only that it did not bind this site.

- **`archive/dev/DD-archived.md`. READ, for W2.** Quote at
  `archive/dev/DD-archived.md:22`:

  > **MAXIMUM REUSE is the architecture's objective, and it is the same rule as WRITE IT GENERIC.**

  This is DD4, the source of clause W2, and it is what made me state
  `hull-closed-op∥` generically rather than writing `Lset` into the one
  proof. The row's "write it generic" absorption is why the file has one
  proof and five corollaries.

- **`archive/dev/LJ-dispatch-index.md`. OPENED AND DECLINED, with the
  reason measured.** Quote at `archive/dev/LJ-dispatch-index.md:1`:

  > # THE `LJ` DISPATCH INDEX, archived 2026-08-18

  **It cannot hold what this task needed: its highest `LJ-1` row is
  `LJ-1.387`**, and the four tasks that bear on this one are `[LJ-1.462]`,
  `[LJ-1.474]`, `[LJ-1.479]` and `[LJ-1.481]`, all later. I read their
  reports in `agents/tasks/` instead. Recording the ceiling so the next
  agent does not pay this lookup again.

- **`dev/ARCHIVE.md`. OPENED AND DECLINED.** Quote at `dev/ARCHIVE.md:3`:

  > The registry of Bedrock's retired modules. One entry per module, written at

  This task retired no module and archived nothing, so the registry has
  nothing to give it and gains no row from it. See W4 above.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md`. READ, AND IT LICENSED
  THE PROOF.** Quote at `dev/literature/truncation-and-selection.md:92`:

  > HoTT Book Lemma 3.9.1: if `P` is a mere proposition then `P ≃ ∥P∥`.

  The file calls this "the only free case" (`:95`). Both truncation
  eliminations in `hull-closed-op∥` are that case: the goal `⟨ F y ∈ˢ M ⟩`
  is a mere proposition, so `PT.rec` enters it with no choice principle.
  **This is why the truncated keystone costs nothing**, which is the
  result `[LJ-1.646]`'s brief most needs.

- **`dev/literature/devlin-II5.md`. READ, AND IT EXPLAINS THE TWO OLD
  NO-GOs.** Quote at `dev/literature/devlin-II5.md:122`:

  > a ∈ M iff for some formula φ(v₀) of ℒ_X, a is the unique element of L_α

  Devlin's hull is defined by UNIQUE definability; Bedrock's is defined by
  least witness and indexed by `Code`. That divergence is the subject of
  "WHY UNIQUENESS WAS THE WRONG QUESTION" above. I also read `:309`:

  > carrier closure (witness inside the carrier, or adequacy) the load-bearing

  which is the classical counterpart of the obligation this task
  discharges, and it is why step 2 is worth its dispatch even at ten lines.

- **`dev/literature/digest.md`. OPENED AND DECLINED.** Quote at
  `dev/literature/digest.md:1`:

  > # Digest: the orthodox form of the rud route, pinned from the collected literature

  Its Skolem-hull material is the J-side, `SZ 1.14-1.15` and the Σ₁ Skolem
  functions every J-structure carries (`:230`). **This task is entirely
  inside the Def-side hull as `src/L/Hull.lagda.md` builds it**, and the
  rud route's hull is a different object with a different membership
  criterion. Taking anything from it here would be transfer by analogy.

- **`dev/literature/terms-2026-08.md`. DECLINED, not read beyond its
  header.** Quote at `dev/literature/terms-2026-08.md:1`:

  > # The terminology dossier: fourteen renderings for the owner's ruling

  It is a translation-terminology dossier feeding `dev/glossary.toml`.
  This task names no new term, adds no glossary entry, and writes no prose,
  so clause W5 is not engaged.

- **`dev/literature/geology.md`. DECLINED, not read beyond its header.**
  Quote at `dev/literature/geology.md:1`:

  > # Geology dossier: set-theoretic geology sources and the five questions

  Set-theoretic geology sources for `[L6]`. Nothing in mantles, grounds or
  the approximation property bears on a ten-line closure corollary inside
  the Skolem hull.

## SCOPE

I wrote only these paths, all inside the brief's SCOPE (write):

- `agents/tasks/LJ-1-647/Probe647.agda`
- `agents/tasks/LJ-1-647/lj-1.647-report.md`
- `agents/tasks/LJ-1-647/runs/` (`run.sh`, `FLOOR.agda.txt`, `W3.agda`,
  and fifteen `.out` records; `final-Probe647.out` and `final-W3.out` are
  the closing conjunct-1 check, both exit 0, on the delivered bytes)

`agents/tasks/LJ-1-647/review-of-hull-closed-lset.md` is NOT written, and
that is deliberate: the verdict is GO, and that file is how a coder states
a NO-GO. Nothing under `src/` was touched. No commit, no push.
