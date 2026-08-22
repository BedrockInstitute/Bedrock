# LJ-1.537 report: the approximating function, as a set of the model

## HEAD
head_slot: coder
machine: shared
verdict: GO

## VERDICT

**GO. `approx-carve` is built, with no holes and no postulate.**
`agents/tasks/LJ-1-537/Probe537.agda:616-620`, exit 0, caliber
`-A64m -I0 -M8g` taken from the pane, one Agda process at a time.
Three cold runs at 2.35 s, 2.29 s and 2.29 s (`runs/full-1.out` to
`runs/full-3.out`; the interface was removed before each).

    approx-carve :
        (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
      → Σ[ f ∈ S ] Approximates a oa m mx f

**THE TYPE IS PINNED IN A SEPARATE MODULE AND CANNOT HAVE DRIFTED FROM THE
BRIEF.** `runs/Pin.agda:46-62` writes the three conjuncts out as satisfaction
of `fnAt`, `assignAt` and `supAt` THEMSELVES, without `[LJ-1.521]`'s `Env`
abbreviations, at the environment `rankFo` puts them in
(`agents/tasks/LJ-1-521/Probe521.agda:493-501`), and inhabits that type by
`P537.approx-carve` and by nothing else. Exit 0, 1.17 s, `runs/pin-1.out`.

**THE CARVED SET IS THE GRAPH THE BRIEF NAMED, AND ONE MORE TERM SAYS SO.**
Satisfying three conjuncts is not the same sentence as being the rank's graph,
so `approx-is-the-rank-graph` (`Probe537.agda:626-633`) states the second one:
for every ∈-predecessor `x` of `m`, the pair `(x , rank-at′ a oa x _)` is a
member of the carved set.

**NOTHING WAS WEAKENED.** The restriction is the ∈-predecessors of `m` and not
a superset; all three properties are proved, not two; nothing lands in `src/`;
`domAt-in` and `domAt` are NOT built; `[LJ-1.521]`'s `Witness` is not imported.
I did not write a `review-of-*.md`, because this is not a stop.

## D-10, BEFORE ANY AGDA

The brief orders the generator and the formula named first, at `file:line`,
and orders a STOP if neither generator can carve the graph.

**THE GENERATOR IS `hasSeparationL` (`src/L/Axioms/Full.lagda.md:144-146`),
OUT OF A BOUND FROM `smallDom` (`src/L/Recursion.lagda.md:133`).** That is
`[LJ-1.521]`'s `Witness` pattern (`agents/tasks/LJ-1-521/Probe521.agda:1046-1059`),
at one component instead of two: `Witness` bounds the SQUARE of the carrier
because its condition relates two members, this carve bounds the carrier
because its condition relates a member to itself
(`Probe537.agda:138-139`).

**AND THE FORMULA I GIVE IT NAMES NO RANK AND NO RECURSION.**

    Cond = ∃̇ ( prAtL (suc zero) zero zero ∧̇ (var zero ∈̇ con m) )

`Probe537.agda:153-157`. Read: "z is the pair of some x with itself, and that
x is a member of m." One existential, two conjuncts, and `con m` is the only
constant.

### why that formula is the right one: THE RANK IS THE MEMBER

`P521.swo-rank′ w k` is `boundingOrd (Pred k) (λ p → swo-rank′ w (p .fst))`
(`Probe521.agda:237-244`), and `boundingOrd X g` holds exactly the members of
the SUCCESSORS of its family (`bnd-out` and `bnd-in`, `Probe521.agda:290-313`).
So

    swo-rank′ w k  =  ⋃ { sucV (swo-rank′ w j) : j ≺ k }.

At this site `w` is `OrdSWO∈ₛ.w α oα` (`Probe521.agda:210-217`) and `≺` is
`_∈ₛ_` (`Probe521.agda:176-177`). So the recursion is
`x ↦ ⋃ { sucV y : y ∈ x }`, and that is the IDENTITY on every transitive set.
Every member of an ordinal is transitive:
`IsOrd A = isTransV A × ((x : S) → ⟨ x ∈ˢ A ⟩ → isTransV x)`
(`src/L/Constructible.lagda.md:141-142`), second component.

**SO THE GRAPH OF `swo-rank′` OVER THE ∈-PREDECESSORS OF `m` IS THE IDENTITY
GRAPH ON `m`, AND THAT IS WHY NO RECURSION HAS TO BE SAID IN THE OBJECT
LANGUAGE.**

**THIS IS NOT A WEAKENING OF THE BRIEF'S TARGET AND THE FILE PROVES IT IS
NOT.** `Ident.rank-id` (`Probe537.agda:283-284`) proves
`swo-rank′ w k ≡ ⟪ α ⟫↪ k` at the sealed rank, and `rank-at′-is-member`
(`:287-293`) carries it to `fst (rank-at′ a oa m mx) ≡ fst m`. The two
descriptions of the set are then the same set, and `approx-is-the-rank-graph`
(`:626-633`) is the sentence that spends the identity rather than dodging it.
**Nothing here unfolds the sealed recursion:** the whole argument spends
`rank-mem-out` and `rank-mem-in`, two of the five names `[LJ-1.521]`'s seal
exports (`Probe521.agda:393-403`, the `opaque` block opening at `:380`).

**IT IS A NEW FACT IN THIS TREE.** I grepped the LJ-1.5xx reports for it and
found no statement that the replacement rank is the member at an ordinal site.
`[LJ-1.515]` proved the rank is `∅` at a minimal element and that a
predecessor's rank is a member (`agents/tasks/LJ-1-515/Probe515.agda:218-231`);
`[LJ-1.531]` proved it injective (`agents/tasks/LJ-1-531/lj-1.531-report.md:1`).
Both are corollaries of the identity, and neither was proved from it.

## W3, THE FORMULA

**GO. 1.10 s, and the estimate was "about 35 lines and under 60 seconds".**

`agents/tasks/LJ-1-537/runs/W3.agda`, module `LJ-1-537.runs.W3`, exit 0, three
cold runs: 1.10 s, 1.09 s, 1.09 s (`runs/w3-1.out` to `runs/w3-3.out`). 159
lines, of which 31 are the head comment and about 75 are code.

The slice carries the formula, the `smallDom` bound, the separated set, and
the two membership directions `graph-in` and `graph-out`, with the three
satisfaction properties OMITTED exactly as the brief ordered, and without the
identity lemma, which is not the formula.

**THE BRIEF'S STOP CONDITION DID NOT FIRE, AND IT IS WORTH SAYING WHY IT
COULD NOT.** The condition was "if the rank's recursion cannot be said in the
object language at this arity". The arity the carve needs is TWO free
variables, against the five `rankFo` already spends
(`Probe521.agda:493-501`), because the recursion is never said at all.

**I DID NOT FUND W3 AGAINST `[LJ-1.518]`'s OR `[LJ-1.521]`'s NUMBERS**, as the
brief ordered. The measurement above is this file, cold, on this pane.

## WHAT THE OBLIGATION COST

**EVERY NUMBER BELOW IS COLD: the file's interface was deleted before each
run**, because a warm run only reads `_build/2.8.0/agda/.../*.agdai` and
measures nothing.

| what was checked | lines | cold | runs |
|---|---|---|---|
| `runs/W3.agda`, `Probe521` warm | 159 | 1.10 s | `w3-1.out` to `w3-3.out` |
| `Probe537.agda`, `Probe521` warm | 633 | 2.29 s | `full-1.out` to `full-3.out` |
| `runs/Pin.agda`, both warm | 64 | 1.17 s | `pin-1.out` |
| `Probe521.agda` ALONE, the baseline | 1176 | 3.80 s | `baseline-521.out` |
| `Probe537.agda` with `Probe521` ALSO cold | 633 + 1176 | 5.05 s | `full-with-521.out` |

**SO THIS FILE'S OWN MARGINAL COST IS 1.25 s** (5.05 minus the 3.80 baseline),
and 2.29 s is what a consumer pays who already has `[LJ-1.521]`'s interface.

**THE BRIEF EXPECTED THIS TO BE BIGGER THAN `[LJ-1.521]` AND IT IS SMALLER.**
Like for like on THIS pane, both cold: `Probe521.agda` alone is 1176 lines at
3.80 s, and adding this file's 633 lines takes the pair to 5.05 s. On its own
pane `[LJ-1.521]` measured itself at 5.30 s
(`agents/tasks/LJ-1-521/runs/full-1.out`), and that number is not comparable
to mine.
**The whole of the difference is the D-10 answer.** Priced the way the brief
imagined it, the formula would have had to express a well-founded recursion at
five free variables and the three satisfaction proofs would have run over it;
priced at the identity, `assignAt` reduces to "a transitive set is the union
of the successors of its members" and `supAt` to the same sentence at `m`.

**THIS FILE IS ALSO SMALLER THAN IT LOOKS.** Of the 633 lines, 48 are the head
comment, 95 are the rebuilt carve (section 1, `:119-213`, which is
`runs/W3.agda`),
and 57 are `readψ` and `fillψ` (`:455-511`), which are `[LJ-1.521]`'s
`asgRead` and `asgFill` (`Probe521.agda:615-666`) with their `extAt` step
removed. That removal is the one thing in the file that is pure transcription
cost: the reader exists, but it consumes the `extAt` this task has to BUILD,
so it cannot be called.

### what resisted

1. **`assignAt`'s de Bruijn depth, and nothing else.** The formula's inner
   body sits six binders deep (`asgσ`, `Probe521.agda:462-463`), and the
   environment a consumer must write out is
   `(s ∷ u' ∷ y ∷ u ∷ v ∷ x ∷ γ5)`. `[LJ-1.521]` had already written that
   environment down twice, in `asgRead` (`Probe521.agda:615-649`) and
   `asgFill` (`:651-666`), and taking those two
   as the template is what made section 4.3 a first-try green. **Had they not
   been in the tree, this would have been the expensive half of the task.**
2. **`Carve.G` is not exported through `Build`.** `open Carve m` inside
   `module Build` does not re-export, so the obligation names `Carve.G m`
   (`Probe537.agda:611`) and not `Build.G`. One scope error, one line, and it
   is the only failure this task recorded (`runs/stage-c.out`, exit 42).

### what did not resist, and I flag it because the brief expected it to

**All three satisfaction properties typechecked on the first attempt**
(`runs/stage-b.out`, exit 0), as did the identity lemma (`runs/stage-a.out`,
exit 0). Those two runs are incremental checks of a partial file against a
warm `Probe521`, so their seconds are NOT prices and I do not quote them as
such; the priced numbers are the cold table above. The task recorded exactly
one red run in total. **I take that as evidence about the D-10 answer and not about the
difficulty of the conjuncts**: the brief's own estimate is the honest price of
the route it named, and the route it named was not the cheapest one available.

## W2, ANSWERED

The brief did not state W2, and I answer it anyway.

**THE MATHEMATICS IS AT THE GENERIC CARRIER WHERE IT CAN BE, AND THE ONE PLACE
IT CANNOT IS NAMED.** `Ident` (`Probe537.agda:222-284`) is parameterized by an
arbitrary `(α , oα)` and not by the coding site, so the identity lemma is
available to any consumer of `P521.swo-rank′` at an ordinal. `Carve`
(`:119-213`) is parameterized by `m` alone and knows nothing about `a`, `Q` or
the rank. `approx-carve-at` (`:600-614`) takes ANY `Q` the hypothesis reads,
and `approx-carve` (`:616-620`) is that term at `[LJ-1.521]`'s witness.

**THE ONE THING THAT IS NOT GENERIC IS THE IDENTITY ITSELF, AND IT MUST NOT
BE.** `swo-rank′` at an arbitrary `SWO` is NOT the identity: the statement
needs the carrier to be an ordinal's members and the order to be ∈. So `Ident`
takes `IsOrd α`, and a consumer at a different well-order gets nothing from
this file. That is a real boundary and not an omission.

## W4, ANSWERED

**NOTHING WAS RETIRED AND NOTHING SHOULD BE.** No module left `src/`, so
`dev/ARCHIVE.md` takes no row from this task.

**PRICED THE OTHER WAY, AS W4 ASKS:** written fresh today, section 1 of this
file would be written exactly as it is (it is `runs/W3.agda`, unchanged but
for three renamed binders); sections 3 and 4 would be written as they are; and
`readψ`/`fillψ` would NOT exist, because `[LJ-1.521]`'s `asgRead` and
`asgFill` would have been split at the `extAt` boundary in the first place.
**That is the one restatement this task's work suggests, it belongs to
`[LJ-1.521]`'s file and not to mine, and I did not make it**, because a probe
does not edit a predecessor's probe.

## WHAT `domAt` NEEDS AFTER THIS

**`domAt-in` IS NOW A COMPOSITION OF DELIVERED TERMS, IN BOTH HALVES, AND I
DID NOT BUILD IT.**

`domAt-in` (`src/L/Coding/Model.lagda.md:294-296`) asks, for a coded `F` and a
member `x` of the domain slot, for a `y` with `pr x y ∈ fst F`. At the coding
site `F` is `fst (rank-graph Q a bnd)`, which is
`hasSeparationL bnd (P521.rankFo Q a) .fst`
(`agents/tasks/LJ-1-529/Probe529.agda:150-154`), so that membership splits into
two obligations, and both are now in the tree.

1. **The satisfaction half, which is the converse `[LJ-1.524]` named**
   (`agents/tasks/LJ-1-524/lj-1.524-report.md:261`). `rankFo Q a`
   (`Probe521.agda:493-501`) at the pair `prʟ x r`, `r := rank-at′ a oa x xa`,
   asks for four existentials and then exactly three conjuncts:
   - `var zero ≐ con Q` at `q := Q`: `refl`.
   - `prAtL (s3 zero) (suc zero) zero`, that the pair splits:
     `prʟ-fst` (`src/L/Coding/Model.lagda.md:329-330`).
   - `var (suc zero) ∈̇ con a`, that `x` is a member of `a`: the hypothesis.
   - `fnAt ∧̇ assignAt ∧̇ supAt` at some `f`: **`approx-carve a oa x xa`,
     this task** (`Probe537.agda:616-620`). Its environment is already the one
     `rankFo` builds, which is what `runs/Pin.agda:46-62` checks.
2. **The bound half.** `pr x r ∈ fst bnd` is `rank-bound′`, delivered by
   `[LJ-1.529]` (`agents/tasks/LJ-1-529/Probe529.agda:133-140`), whose
   statement is at `swo-rank′ w (fiber (fst a) mx .fst)` and reaches
   `rank-at′` through `P521.rank-at′-val` (`Probe521.agda:438-442`).

**SO `domAt` CLOSES WITH IT.** `domAt-out` was already delivered
(`[LJ-1.524]`, `lj-1.524-report.md:277-279`), and `domAt-intro`
(`src/L/Coding/Model.lagda.md:298-305`) takes the two directions and nothing
else. **I state that as a reading of the types and not as a measurement: I did
not build it, the brief forbids it, and the next task should expect the
de Bruijn transcription of `rankFo`'s four existentials to be its real cost.**

**ONE CAVEAT THE NEXT BRIEF MUST CARRY.** `approx-carve` is stated at
`Qwit a oa`, `[LJ-1.521]`'s own witness (`Probe521.agda:1162-1164`). If the
coding site's `Q` is a different set, use `approx-carve-at`
(`Probe537.agda:600-614`), which takes any `Q` with `ord-reads-Q Q a oa`. The
general form is there for exactly that reason.

## THE IMPORT OF A PREDECESSOR PROBE

**ONE, AND IT IS `[LJ-1.531]`'s NECESSITY VERBATIM**
(`agents/tasks/LJ-1-531/Probe531.agda:20-37`). `P521.swo-rank′` is sealed
(`Probe521.agda:380-403`) and this file needs two of the five names the seal
exports. It also needs the FORMULA the obligation is stated at, `fnAt`,
`assignAt` and `supAt` (`Probe521.agda:456-491`), and `Env`'s five slots
(`:512-516`): a rebuild would not merely cost 1176 lines, it would state the
obligation at a DIFFERENT `fnAt`, and `[LJ-1.521]`'s consumers would get
nothing. `bedrock.agda-lib:2` lists `agents/tasks` as an include root.

## GATES RUN

`scripts/gate/lint-prose.py --check`, `scripts/gate/lint-agda.py --check`,
`scripts/gate/check-probes.py --check` (clean, 5866 tracked files) and
`scripts/pod/check-closure.py --check closure` (clean, 102 masters), each exit
0, run as `/Users/alsg/Agentic/Bedrock/.venv/bin/python` because this worktree
carries no `.venv`. **I did not commit and did not push.**

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: READ. `:361` says
  "| LJ-1.304 | Price StepAgree and ApproxAgree | BOTH BUILT, ABOUT 190 LINES. BASIS: THE BUILD | q's four named costs are now ALL measured. Neither module exists in src/: they were LJ-1.52's names |".
  I read it because "ApproxAgree" is the only earlier name in the tree close to
  this task's "approximating function", and it is NOT this: it is a
  `[LJ-1.52]` name for a module that never landed in `src/`. Nothing to reuse
  and nothing to collide with.
- `dev/ARCHIVE.md`: READ. `:89` says
  "| `archive/src/2026-08-13-probe-sweep/` | **Empty since 2026-08-13.** A tombstone that maps 257 pre-ruling probe paths to their homes in `agents/tasks/<TASK>/` | `archive/src/2026-08-13-probe-sweep/README.md` |".
  I read it to confirm where a probe of this task belongs before I wrote one.
  All three `.agda` files of this task are under `agents/tasks/LJ-1-537/`.
- `archive/dev/JOURNAL.md`: NOT READ, declined. I searched it for
  `approximating`, `swo-rank`, `rankFo` and `assignAt` and it names none of
  them; a journal of closed work cannot carry a type this task must match.
- `archive/dev/JOURNAL-archived.md`: NOT READ, declined, same search and same
  reason.
- `archive/dev/DECISIONS-archived.md`: NOT READ, declined. It is the archived
  `D<n>` series, which memory and `dev/memos/LJ-4-pod-program-design.md`
  section 7.1 both mark as not in force; no clause of it binds a carve.

## LITERATURE USED

- `dev/literature/digest.md`: READ. `:218` says
  "  and J_α^A = S_α^A at limit α (I.1); the rank jump per S-step is finite."
  I read it for the same reason `[LJ-1.521]` did
  (`agents/tasks/LJ-1-521/lj-1.521-report.md:540`): to confirm that the rank
  this task carves is NOT the fine-structural rank of the `J`/`S` hierarchy.
  It is not. This task's rank is the ∈-rank of a well-order on one ordinal's
  carrier, and section D-10 shows it is the identity there, which the
  fine-structural rank is not.
- `dev/literature/devlin-II5.md`: READ. `:445` says
  "statement is π(x) ≤_L x, the collapse never raises the <_L-rank."
  Read for the same separation: `<_L` is the global order on `L`, this task's
  order is ∈ on the members of one ordinal, and the identity finding does not
  transfer to `<_L`.
- `dev/literature/truncation-and-selection.md`: NOT READ, declined. The carve
  here truncates nothing and selects nothing: `hasSeparationL` returns an
  `isContr`, so there is no choice to make.
- `dev/literature/terms-2026-08.md`: NOT READ, declined. It is a naming
  dossier, and this task added no `dev/glossary.toml` entry and coined no
  term.
- `dev/literature/geology.md`: NOT READ, declined. Set-theoretic geology bears
  on no part of this carve.
