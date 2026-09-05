# LJ-1.652 report: pi commutes with the definable powerset, from elementarity

## HEAD
slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-652/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M2g"`, the wide caliber, ONE Agda process at a time.
I did not set `GHCRTS`. No heap event: the largest peak of any run is
1,083,228,160 bytes against the 2,147,483,648-byte cap.

TARGET: build ONE term in `agents/tasks/LJ-1-652/Probe652.agda`:

    picommute-D-from-elem :
        <Elementary as a HYPOTHESIS>
      → <[LJ-1.651]'s lset-formula, and its 𝒟ₒ counterpart, as HYPOTHESES>
      → (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (𝒟ₒ y) ≡ 𝒟ₒ (C.π y)

Nothing lands in `src/`. Neither hypothesis is built.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work. It
does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**NO-GO at the brief's hypothesis list, and a GO beside it.**

- **NO-GO.** `picommute-D-from-elem` is not written. Elementarity,
  `lset-formula` and its `𝒟ₒ` counterpart do not produce it. Exactly one
  more thing is needed and it is named, typed and printed by Agda:
  `DeeInHull = (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ 𝒟ₒ y ∈ˢ M ⟩`
  (`Probe652.agda:280-281`, and `runs/residue-1.out:4`). The stated
  NO-GO is `agents/tasks/LJ-1-652/review-of-picommute-D.md`. That file
  is the critic's input and it does not close the task.
- **GO, unasked.** Clause (iii)'s `Commute`, at `[LJ-1.641]`'s own type,
  IS closed by this task from elementarity and `lset-formula` alone:
  `commute-641 : Matrix₂ Lset → F641.Commute` (`Probe652.agda:305-306`),
  checked against `[LJ-1.641]`'s module and not against my copy of its
  lines. No keystone, no `RankInHull`, no `CommuteAtSuc`.

Witness meter, the obligation: `1 UNRESOLVED of 1, 3.07 s,
probe_red=False` (`runs/meter-obligation.out:2`). Witness meter, the
nineteen delivered names: `0 UNRESOLVED of 19, 3.52 s, probe_red=False`
(`runs/meter-names.out:20`). The probe is green and carries no hole
(`runs/p-final.out:2`).

**This is not a refutation of `PiCommuteD`.** I did not build a term of
its negation. The statement is true about the real hull.

## THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The brief names `[LJ-1.651]`'s `lset-formula` as a hypothesis. **That
task has delivered nothing, and its task home does not exist in this
worktree at all.** `ls agents/tasks/LJ-1-651/` fails here, and
`dev/pod/queue.toml` carries no `651` entry either, so there is no
in-worktree path I can cite for it. It is a SIBLING admitted one commit
before this task (`git log --oneline`: `a8bf4224 pod: admit LJ-1.651`,
`d3e3ebe3 pod: admit LJ-1.652`), not a predecessor.

So the standing clause "a module hypothesis taken from a predecessor is
the type that predecessor delivered" has no delivered type to take, and
I say so rather than pretending one exists. `[LJ-1.648]` met the same
situation and recorded it under "THE PREDECESSOR QUESTION".

I read the sibling's brief in the MAIN CHECKOUT, outside this worktree,
at `/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-651/LJ-1.651.md:11-12`:

    lset-formula : <a `Formula Code 1` over the hull's code alphabet that holds
                    exactly of the `Lset` of its parameter, built as a Σ₀ matrix

**That path is not inside this worktree and a checker cannot open it
from here.** Everything this file DEPENDS on is stated in this task's own
brief instead (`agents/tasks/LJ-1-652/LJ-1.652.md:13-14`), which names
the two objects, and the shape is settled against the tree and the
literature rather than against the sibling.

**AND I HEDGED IT.** Because the sibling's shape is not settled, every
consumer in this file is built at BOTH plausible shapes, `Matrix₂` and
`Witnessed`, so nothing here has to be rebuilt whichever one lands.

## D-10, BEFORE ANY AGDA

D-10 says to price the truth of the target before pricing its proof.
**The target is not the thing at risk here. The HYPOTHESIS is.**

1. The target. `PiCommuteD` is Devlin's condensation step and it is
   true. `dev/literature/devlin-II5.md:102-104` runs the chain by
   elementarity and the collapse, not by a computation law. I did not
   find a cardinality or Tarskian obstruction to it.
2. The hypothesis. `Matrix₂ F` (`Probe652.agda:75-85`) asks for a
   two-slot Δ₀ parameter-free formula whose ambient reading is exactly
   the graph of `F`. **The literature says that object does not exist.**
   `dev/literature/devlin-II5.md:95`:

       > By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that

   and `:96`:

       > (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]

   The Σ₀ form has a WITNESS slot. The graph is `∃z Φ`, which is Σ₁.
   A two-slot Δ₀ matrix for the graph would make the graph Δ₀.
3. So I recorded the corrected target beside the original, as D-10 asks:
   `Witnessed F` (`Probe652.agda:87-92`) is Devlin's shape, and
   `commute₃` (`:215-224`), `commute-from-witnessed` (`:266-268`) and
   `picommute-D-from-witness` (`:292-293`) are the consumers at it.

**This is the finding `[LJ-1.651]` most needs**, and it is about that
task's own target, not mine. What this task adds is the
CONSUMER'S requirement: a formula alone is not enough, the consumer
needs it Δ₀, because Δ₀ is what crosses into the collapse.

## THE FLOOR, AND HOW IT WAS TAKEN

The standing clause asks for the frame to be priced before the proof.

- **The frame was priced first.** `runs/frame-0.out`: the imports, the
  ambient reading `_⊨ₚ_` and the absoluteness step `AtTrans.read`, with
  no consumer written. Exit 0, 3.82 s, peak 702,611,456 bytes. Every
  later run stayed inside 1.1 GB, so no restructuring was ever needed
  and no heap wall was met.
- **The hole floor came at the END, and its job was different.**
  `runs/FLOOR.agda.txt` states the brief's obligation at the brief's own
  hypothesis list with ONE hole. Exit 42 at the one designed hole
  (`runs/floor-1.out:2`), 4.82 s, peak 1,004,257,280 bytes.
  `runs/RESIDUE.agda.txt` is the same file with a deliberately wrong
  witness, so that Agda PRINTS the type it wanted
  (`runs/residue-1.out:4`):

      when checking that the expression y∈M has type ⟨ 𝒟ₒ y ∈ˢ F.HS.M ⟩

  **Both files are `.agda.txt` and neither claims to typecheck.** The
  brief's warning about `[LJ-1.636]` and `[LJ-1.643]` is answered:
  `find agents/tasks/LJ-1-652 -name '*.agda'` returns `Probe652.agda`
  and nothing else.

## W3, AND ITS QUESTION IS ANSWERED SIDEWAYS

The brief's W3: "Whether `𝒟ₒ`'s defining condition is a
`Formula A.SM n`, which is what `Elementary` transfers." Estimate 80 to
170 lines.

**IT DOES NOT HAVE TO BE, AND MAKING IT ONE IS FREE.** `Elementary`
takes a `Formula A.SM n`, but a parameter-free matrix becomes one by
`embed`, and `embed-map` (`Probe652.agda:56-61`) is the three-line fact
that a parameter-free formula is FIXED by every relabelling. So the same
matrix is read at four alphabets in this file (`⊥*`, `ASt.SL`, `A.SM`,
`CIso.I.SPM`) at no cost at all, and the question W3 asked never
becomes a price.

The question that DOES cost is the one D-10 found: not which alphabet,
but how many SLOTS. Two slots or three decides whether the hypothesis
exists at all.

Line count: 306 total, 156 non-blank non-comment
(`Probe652.agda`). That is inside the 80-to-170 estimate.

## WHAT WAS BUILT

All in `agents/tasks/LJ-1-652/Probe652.agda`, module
`LJ-1-652.Probe652 {ℓ} (lem)`. The frame `Frame652` (`:99-105`) is the
telescope of `src/L/BoundedSubset.lagda.md:903-914` verbatim, as
`[LJ-1.641]` and `[LJ-1.648]` cut it, plus `module A = ASt.AtM HS.M
HS.H.Hull⊆L`, which is where `Elementary` lives.

**Top level.**

- `embed-map` (`:56-61`). A parameter-free formula is fixed by every
  relabelling. Used at three different maps.
- `Matrix₂` (`:75-85`). The brief's reading of `[LJ-1.651]`.
- `Witnessed` (`:87-92`). Devlin's shape.

**Section 1, the absoluteness step, at a GENERIC transitive carrier.**

- `AtTrans.read` (`:118-124`). The inner reading of an embedded Δ₀
  matrix is the ambient reading. `abs₀`
  (`src/FOL/Absoluteness.lagda.md:122`), `mapΔ₀`, `embed-⊨` and one
  `funExt` over the empty constant domain.

**Section 2, the carry. THIS IS WHAT ELEMENTARITY BUYS.**

- `Mext` (`:152-153`). `isExt HS.M` is NOT a hypothesis of this file:
  `hullExt` (`src/L/BoundedSubset.lagda.md:1340`) is green in the tree.
  `AtHullInstance` takes it as a parameter (`:772`); it did not have to.
- `atL` (`:162-164`), `atπ` (`:166-168`). The same lemma at the stage
  and at the collapse. Both carriers are transitive.
- `atM` (`:171-183`). The hull is NOT transitive, so absoluteness is
  unavailable and `elem` is what replaces it. This is `[LJ-1.489]`'s
  missing ingredient, spent.
- `push` (`:185-192`). Ambient truth at hull members becomes ambient
  truth at their collapse values, at EVERY arity and EVERY Δ₀
  parameter-free formula.

**Section 3, the consumers, at a GENERIC operation.**

- `commute₂` (`:206-211`). `π (F y) ≡ F (π y)` from `Matrix₂ F`, at any
  hull member `y` with `⟨ F y ∈ˢ M ⟩`. ONE side condition, and it is the
  only one.
- `commute₃` (`:215-224`). The same at `Witnessed F`, where the residue
  also carries the witness.

**Section 4, the two instances.**

- `Commute` (`:249-253`) and `commute-from-lset-formula` (`:255-257`).
- `LsetGrounded` (`:260-264`) and `commute-from-witnessed` (`:266-268`).
- `PiCommuteD` (`:273-275`), `[LJ-1.489]`'s type.
- `DeeInHull` (`:280-281`) and `picommute-D-from-hull` (`:283-284`).
- `DeeGrounded` (`:286-290`) and `picommute-D-from-witness` (`:292-293`).
- `commute-641` (`:305-306`). `Commute` checked against
  `[LJ-1.641]`'s own module.

## THE THREE FINDINGS, EACH WITH ITS EVIDENCE

**FINDING 1. ELEMENTARITY REACHES `𝒟ₒ`. THE HULL'S CLOSURE UNDER `𝒟ₒ`
IS WHAT IT DOES NOT REACH.** `[LJ-1.489]` said the two sides cannot
agree without elementarity (`agents/tasks/LJ-1-489/lj-1.489-report.md:139-140`)
and the brief read that as "elementarity is the missing ingredient".
Half right. The transfer elementarity opens is `push` (`:185-192`) and
it is green, generic and cheap. What it leaves is `⟨ 𝒟ₒ y ∈ˢ M ⟩`, and
Agda prints that type (`runs/residue-1.out:4`).

**FINDING 2. `Commute` CLOSES AND `PiCommuteD` DOES NOT, AND THE
DIFFERENCE IS THE TYPE, NOT THE MATHEMATICS.** `Commute`
(`agents/tasks/LJ-1-641/Probe641.agda:69-73`) carries
`(Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)` as its OWN hypothesis, which is exactly
`commute₂`'s side condition at `F := Lset`. `PiCommuteD`
(`agents/tasks/LJ-1-489/Probe489.agda:139-141`) is stated at a general
hull member and carries nothing. Same proof, same operation shape,
different bookkeeping in the statement, opposite outcomes.

This corrects the brief's premise 4 downward and upward at once.
`[LJ-1.648]` measured that `DefFwd` and `DefBwd` are `[LJ-1.489]`'s
statement. **The half of it clause (iii) consumes is `Commute`, and
`Commute` is now closed.** The other half, `[LJ-1.489]`'s general
statement, still owes `DeeInHull`.

**FINDING 3. THE RESIDUE IS A SEARCH `hull-closed` CAN ANSWER, AND IT IS
THE KEYSTONE'S OWN SHAPE.** `[LJ-1.648]`'s language argument
(`agents/tasks/LJ-1-648/review-of-commute-from-keystone.md`, part 3)
killed `DefBwd` because its condition names `π`, which is not a term of
the hull's language. **`DeeInHull` names no `π`.** And `[LJ-1.648]`
measured the keystone to be exactly `HullClosedLsetOrd`
(`agents/tasks/LJ-1-648/Probe648.agda:203-213`), which is `DeeInHull`
with `Lset` for `𝒟ₒ` and an ordinality side condition added. So the
residue is a `𝒟ₒ`-keystone and it is dispatchable today.

## WHAT THE KEYSTONE ROUTE TO THE RESIDUE COSTS, AND WHERE IT STOPS

I did not build `DeeInHull` and the brief did not ask me to. I priced
its route far enough to name the obstruction, so the next brief does not
have to rediscover it.

`hull-closed` (`src/L/Hull.lagda.md:415`) takes a `Formula Code 1`. The
matrix has two or three slots, so the parameter slot must be closed at
the code of `y`. `CloseSyntax.close` is the tree's operation for that
(`src/L/BoundedSubset.lagda.md:533-535`) and **it cannot be applied at
`Code`**: its carrier is `{K : Type (ℓ-suc ℓ)}`
(`src/L/BoundedSubset.lagda.md:508`) and `Code` is `Type ℓ`
(`src/L/Hull.lagda.md:72`). The tree's own way around this is
`HullElemDown.WithCode` (`src/L/BoundedSubset.lagda.md:681-683`), which
closes over `A.SM` and then relabels by a CODE MAP `f : A.SM → Code`.
So the residue's route needs a code map, which is the object
`[LJ-1.647]` closed for `Lset`, and it also needs the existential
witness `⟨ 𝒟ₒ y ∈ˢ Lset lam ⟩`. **I found no lemma in the tree that puts
`𝒟ₒ y` in a stage for a general `y`:** every `𝒟ₒ` lemma of
`src/L/Axioms/Basic.lagda.md` takes `Lset β` as its argument
(`:98`, `:196`, `:230`, `:352`, `:547`).

## W2 (DD4)

The mathematics is written once at a generic carrier and instantiated,
and this task is unusually well served by that rule.

- `AtTrans` (`:114-124`) is generic in the TRANSITIVE CARRIER. It is
  instantiated at `Lset lam` and at `HS.C.πX`.
- `Carry.push` (`:185-192`) is generic in the ARITY and in the Δ₀
  FORMULA. It is instantiated at two slots and at three.
- `Op.commute₂` and `Op.commute₃` (`:206-224`) are generic in the
  OPERATION. They are instantiated at `Lset` and at `𝒟ₒ`.

**Clause (iii)'s `Commute` and this task's obligation are the SAME term
at two operations.** No line of mathematics is written twice. The
deadline conflict the clause names did not arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`. No dead fragment was
deleted. `dev/ARCHIVE.md` gains no row from this task.

## C-42

No refutation was produced, so the sweep this law demands does not fire.
I did not count live `src/` occurrences of a false shape, because no
false shape was proved. The one shape worth counting, if the pod ever
does refute `Matrix₂`, is a `Formula` hypothesis stated without a Δ₀
certificate; this file states none such.

## RUNS

Caliber `-A64m -I0 -M2g`, set on the pane by the program and untouched
here. One Agda process at a time, from the worktree root. The probe
interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-652/Probe652.agdai`).

Build history, in order:

| run | contents | exit | wall s | peak RSS bytes |
|---|---|---|---|---|
| `frame-0` | imports, `_⊨ₚ_`, `AtTrans.read` | 0 | 3.82 | 702,611,456 |
| `s2-0` | + section 2, first attempt | 42 | 3.12 | 544,587,776 |
| `s2-1` | same, one name qualified | 0 | 3.87 | 681,721,856 |
| `s2-2` | `Mext` from `hullExt`, hypothesis dropped | 0 | 4.28 | 731,037,696 |
| `s3-0` | + `Witnessed`, `commute₃`, generic `push` | 0 | 4.41 | 919,519,232 |
| `s4-0` | + section 4 | 0 | 4.56 | 826,146,816 |
| `s5-0` | + `LJ-1-641.Probe641`, that file COLD | 0 | 6.05 | 1,083,228,160 |

`s2-0` is the only red run of the build and its error is `[NotInScope]`
for `A.⊨ᵐ`: `AtM` renames `_⊨_` without `public`
(`src/L/Hull.lagda.md:169`), so the hull's satisfaction is reached
through `CollapseIso.I` instead (`src/L/BoundedSubset.lagda.md:177`).
One name changed. No restructuring, and no heap event at any point.

Three forced rechecks of the final file, `Probe641` warm:

| run | exit | wall s | peak RSS bytes |
|---|---|---|---|
| `runs/full-recheck-1.out` / `.time` | 0 | 5.35 | 901,627,904 |
| `runs/full-recheck-2.out` / `.time` | 0 | 4.73 | 901,644,288 |
| `runs/full-recheck-3.out` / `.time` | 0 | 4.92 | 901,660,672 |

Median wall **4.92 s**. Median peak RSS **901,644,288 bytes**. Exit 0
every time, each printed `Checking`.

`runs/p-final.out` is the last check of all, run after every comment and
citation in this file was settled: exit 0, 5.14 s, 901,709,824 bytes.

Floor and residue: `runs/floor-1.out` exit 42 at the one designed hole,
4.82 s, 1,004,257,280 bytes; `runs/residue-1.out` exit 42 with the
residue type printed at `:4`, 5.07 s, 426,934,272 bytes.

Meters: `runs/meter-obligation.out` `1 UNRESOLVED of 1, 3.07 s`;
`runs/meter-names.out` `0 UNRESOLVED of 19, 3.52 s`. This worktree has
no `.venv`, so the meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

Gates run while working: `scripts/gate/lint-agda.py --check` exit 0,
`scripts/gate/check-probes.py --check` clean, 9907 tracked files.

## WHAT THE NEXT BRIEF NEEDS

1. **FOR `[LJ-1.651]`, THE SHAPE QUESTION IS THE WHOLE QUESTION, AND IT
   IS SLOTS AND NOT ALPHABET.** The consumer needs the matrix Δ₀,
   because Δ₀ is the only thing that crosses into the collapse
   (`atπ`, `Probe652.agda:166-168`). The alphabet costs nothing
   (`embed-map`, `:56-61`). The literature offers three slots, not two
   (`dev/literature/devlin-II5.md:95-96`). **Ask that task for
   `Witnessed`, not for `Matrix₂`**, and expect the witness to come back
   as a further debt in the hull.
2. **CLAUSE (iii)'s `Commute` IS CLOSED. DO NOT RE-DISPATCH IT.**
   `commute-641` (`Probe652.agda:305-306`) delivers `[LJ-1.641]`'s own
   type from elementarity and `lset-formula`. `[LJ-1.641]`'s three gaps,
   `[LJ-1.648]`'s `RankInHull × CommuteAtSuc`, and the keystone are all
   superseded FOR THIS ONE STATEMENT. What is not superseded is the
   hypothesis: `lset-formula` must exist.
3. **THE NEXT DISPATCH IS A `𝒟ₒ`-KEYSTONE, AND IT IS A SEARCH.**
   `DeeInHull = (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ 𝒟ₒ y ∈ˢ M ⟩`. Its condition
   names no `π`, so `[LJ-1.648]`'s language argument does not bite. Its
   route through `hull-closed` needs two things this task priced and did
   not build: a CODE MAP at `A.SM` (because `CloseSyntax.close` cannot
   be applied at `Code`, `src/L/BoundedSubset.lagda.md:508` against
   `src/L/Hull.lagda.md:72`), and `⟨ 𝒟ₒ y ∈ˢ Lset lam ⟩` for a general
   hull member, for which the tree has no lemma at all.
4. **`⟨ 𝒟ₒ y ∈ˢ Lset lam ⟩` MAY BE THE REAL DEBT AND IT IS A TOWER FACT,
   NOT A HULL FACT.** Every `𝒟ₒ` lemma in `src/L/Axioms/Basic.lagda.md`
   takes `Lset β` as its argument. Price its truth before pricing its
   proof: it is "the stage is closed under the definable powerset at a
   limit", and it needs the definable subsets of an arbitrary member to
   be definable over a later stage.
5. **`Carry.push` IS THE ASSET, NOT `commute₂`.** It is generic in
   arity, in the formula and in nothing else, and it is the mechanised
   form of Devlin's transfer chain
   (`dev/literature/devlin-II5.md:102-104`). Any future statement of the
   form "an ambient Δ₀ fact at hull members survives the collapse" is
   one application of it. `src/L/BoundedSubset.lagda.md` may want it
   after `[LJ-1.651]` lands. This task's scope forbids `src/`.
6. **WHAT THE STATEMENT COST.** 156 non-blank non-comment lines, median
   4.92 s, median peak 901,644,288 bytes, one red run, no heap event.
   **WHAT THE SHAPE RESISTED.** One thing only: `AtM` renames its
   satisfaction without `public` (`src/L/Hull.lagda.md:169`), so the
   hull's `_⊨ᵐ_` has to be reached through `CollapseIso.I`
   (`src/L/BoundedSubset.lagda.md:177`). **WHAT I HAD TO WEAKEN.**
   Nothing of the obligation. I did not weaken the statement, I named
   what it still needs. **WHAT I COULD NOT CLOSE.** `picommute-D-from-elem`,
   `DeeInHull`, `DeeGrounded`, `LsetGrounded`, and either matrix.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. The predecessors this task reads are
  live task homes under `agents/tasks/`.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used. It
  records the retired route; this obligation is on the live one.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. The per-episode journal is retired and the history
  of this task is this directory.
- `dev/ARCHIVE.md`: read at `:1`. Quote:
  `# ARCHIVE.md: the archive registry`. Declined as not used for the
  term. W4 did not fire: no module is retired by this task, so the
  registry gains no row.
- `archive/dev/ORCHESTRATION.md`: read at `:1`. Quote:
  `# ORCHESTRATION: the orchestrator's operating rules`. Declined, not
  used. It is the archived operating document; the rules that bind this
  slot are `AGENTS.md` and `dev/pod/instructions/coder.md`.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **USED, and it decided the D-10
  finding.** Read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`
  Also read at `:96`. Quote:
  `> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`
  Also read at `:102`. Quote:
  `The chain (c) to (q) then runs: for each ordinal γ of the collapse, the Σ₁`
  This is where `Witnessed` (`Probe652.agda:87-92`) comes from, and the
  chain at `:102-104` is what `Carry.push` (`:185-192`) mechanises.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. The one truncation in this file
  (`commute₃`, `Probe652.agda:220`) is eliminated into a path in a set
  by `PT.rec` and `isSetS`, so no selection question arises.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted; this obligation is
  on the definable-powerset tower.
- `dev/literature/geology.md`: read at `:1`. Quote:
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Declined, not used. No grounded-model or geology question is at issue.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`. Declined, not used.
  No glossary term is at issue and I added no `dev/glossary.toml` entry.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`. I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `picommute-D-from-elem`.
- I did not inhabit `Matrix₂` or `Witnessed` at either operation. The
  brief forbids building either hypothesis.
- I did not inhabit `DeeInHull`, `DeeGrounded` or `LsetGrounded`.
- I did not refute `PiCommuteD`.
- I did not postulate. I left no hole in `Probe652.agda`.
- I did not leave a red `.agda` under this task home: the two files that
  cannot typecheck are `runs/FLOOR.agda.txt` and `runs/RESIDUE.agda.txt`.
- I did not add a dependency and I did not create a local `.venv`.
- I did not read a running sibling's output: `[LJ-1.651]` has none.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/` untouched.

New files, all in `agents/tasks/LJ-1-652/`:

- `Probe652.agda`, the carry and the two instances, green
- `lj-1.652-report.md`, this report
- `review-of-picommute-D.md`, the stated NO-GO
- `runs/`, the Agda transcripts and the two `.agda.txt` slices named above
