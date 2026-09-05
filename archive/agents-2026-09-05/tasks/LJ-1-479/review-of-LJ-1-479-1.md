# LJ-1.479: adversarial review of the LJ-1.479#1 return

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

The return under attack is `agents/tasks/LJ-1-479/lj-1.479-report.md`
with its stated NO-GO
`agents/tasks/LJ-1-479/review-of-HullClosedLset.md`. The critic is not
the author of either file. I read the brief
`agents/tasks/LJ-1-479/LJ-1.479.md`, the probe
`agents/tasks/LJ-1-479/Probe479.agda`, every transcript under
`agents/tasks/LJ-1-479/runs/`, and every `file:line` the return names.
I ran `grep -rn "→ IsOrd" src/` and read every hit, to test the
return's enumeration of `IsOrd` sources by my own search and not by
its word.

## THE RECORD THE BRIEF NAMED, AND WHAT IT HOLDS

The brief told me to read the six facts, `model`, `effort` and
`heads_sha256` of the LJ-1.479 instance in `dev/pod/transitions/`.
That record does not exist. `dev/pod/transitions/2026-08.jsonl` has 157
lines. Its last line is dated 2026-08-19 and names another task. Quote
at `dev/pod/transitions/2026-08.jsonl:157`:
`"task": "LJ-1.399", "tier": "wide", "to": "RETURNED"`. No line of
that file names LJ-1.479. This is a gap in the program's record, not a
defect in the return. The same facts exist elsewhere and I used them:

- The facts block is at `agents/tasks/LJ-1-479/runs/accept-1.out:24`.
  It holds `exit_code 0`, `error_class null`, `heap_wall false`,
  `lines 0`, `obligations_delta 0`, `obligations_open 1`, `seconds 2.4`,
  and the 22 changed files. Line 22 of the same file reads `# exit 0`
  and line 19 reads `# obligations delta 0`.
- `heads_sha256` is at `agents/tasks/LJ-1-479/.pod:1`:
  `heads=5f21351997d2d0ae92acbfc5b09358ff8e40cd5adbcef12f919e70fbc38b4fb8`.
- `model` and `effort` for this instance are recorded nowhere I can
  resolve. I searched `dev/pod/transitions/`, `dev/pod/heads.toml` and
  `agents/tasks/LJ-1-479/`. I report the absence and proceed on the
  facts that do resolve.

The facts that do resolve agree with the return: exit 0, no error
class, obligations delta 0, one obligation still open. The dispatch to
this slot came from the `stop-stated` branch, exactly as the return's
NO-GO file says it would.

## QUESTION 1: DOES THE VERDICT LINE MATCH THE BODY

The verdict line is at `agents/tasks/LJ-1-479/lj-1.479-report.md:84`:
`**NO-GO at uniqueness.** `pins` typechecks. It is `Lset-only`. The`.
Read with lines 85 to 88, it claims four things: `pins` typechecks;
the extra `IsOrd` has no source at a hull member; `pins-no-ord` and
`hull-ord` are stated and unbuilt; the obligation term is not written.
I checked each claim against the body and against the tree.

- `pins` typechecks. `pins = Lset-only` stands at
  `agents/tasks/LJ-1-479/Probe479.agda:54`. Three forced rechecks exit
  0 (`runs/w3-1.out` to `runs/w3-3.out`, each one line, the Agda
  `Checking` line and no error).
- `Lset-only` carries the extra `IsOrd` on the argument slot. The type
  is at `src/L/Hierarchy.lagda.md:334`:
  `  Lset-only : ⟨ γ ⊨ LsetGraphAt w b ⟩ → IsOrd (fst (lookup b γ))`.
  The demand is structural, not cosmetic. The proof spends it twice:
  `step-lset` demands it at `src/L/Hierarchy.lagda.md:191`:
  `  step-Lset : ⟨ γ ⊨ StepAt v b f ⟩ → IsOrd (fst (lookup b γ))`, and
  `approx-val` demands it at `src/L/Hierarchy.lagda.md:274`:
  `  approx-val : ⟨ γ ⊨ ApproxAt f a ⟩ → IsOrd (fst (lookup a γ))`.
  The sibling uniqueness lemma `approx-uniq` at
  `src/L/Hierarchy.lagda.md:301` demands the same hypothesis. The
  `IsOrd` cannot be dropped from the delivered reading.
- No source at a hull member. My own search, below in Question 3,
  confirms this on the live tree.
- The obligation term is not written. `HullClosedLset` exists only as
  a type at `agents/tasks/LJ-1-479/Probe479.agda:109-111`. The witness
  meter confirms it: `runs/witness.out:2` reads
  `witness: 1 UNRESOLVED of 1, 2.13 s, probe_red=False`, with a
  `[NotInScope]` at the module root on line 1.

One sentence of the body is looser than the rest. Line 79 reads
`Uniqueness therefore fails at the stated type. `wit`'s value need not`.
What fails is the derivation of uniqueness from delivered lemmas, not
the proposition. The body corrects itself at line 90:
`This is an obstruction of the `wit` then `inHull` join. It is not a`,
and again at lines 274 to 276 under C-42. The verdict line does not
inherit the loose reading: it says NO-GO at uniqueness, and both files
say plainly that no refutation was built. The line matches the body.
The loose sentence is a wording defect. It does not change the verdict
and I do not overturn on it.

## QUESTION 2: DOES EVERY LOAD-BEARING CLAIM RESOLVE

I opened every `file:line` the return and its NO-GO file name. All of
them resolve today. The load-bearing ones:

- `src/L/Hull.lagda.md:74`, the `wit` constructor:
  `    wit  : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec Code k → Code`.
  `search` picks the least satisfier at `src/L/Hull.lagda.md:81`, so
  `val (wit k ψ cs)` is a satisfier chosen by a well order and not by
  the formula's meaning. The D-10 premise of the return is correct.
- `src/L/Hull.lagda.md:117`, `inHull`:
  `  inHull : (c : Code) → ⟨ toSet (val c) ∈ˢ Hull ⟩`. Membership of
  `val (feed c)`, not of `Lset y`, exactly as the return reads it.
- `src/L/Hierarchy.lagda.md:334-335`, `Lset-only`, quoted above.
- `src/L/Ordinal.lagda.md:221`, `mem-ord`:
  `mem-ord : ∀ {A} → IsOrd A → (x : S) → ⟨ x ∈ˢ A ⟩ → IsOrd x`. It
  needs the container to be an ordinal. `Hull⊆L` at
  `src/L/Hull.lagda.md:330` concludes `⟨ x ∈ˢ Lset α ⟩`, and a level
  `Lset α` is not an `IsOrd` container: `IsOrd` at
  `src/L/Constructible.lagda.md:142` is
  `IsOrd A = isTransV A × ((x : S) → ⟨ x ∈ˢ A ⟩ → isTransV x)`, and a
  level with a pair in it has a non-transitive member. So the return's
  claim that `mem-ord` does not apply is right.
- `src/L/Ordinal.lagda.md:258`, `ω-mem-ord`,
  `src/L/BoundedSubset.lagda.md:813`, `isOrdAt-out`, and
  `src/L/BoundedSubset.lagda.md:939`, `β-ord`, all resolve, and none
  takes `⟨ y ∈ˢ M ⟩`. `β-ord` sits inside `module Condense`, after
  `levelIn`, as the return says.
- `src/L/BoundedSubset.lagda.md:917`, `levelIn` as an unpaid hypothesis
  of `module Condense`, with `cover` at lines 918 to 919. Resolves.
- The telescope copy, `src/L/BoundedSubset.lagda.md:903-914` against
  `agents/tasks/LJ-1-479/Probe479.agda:84-96`. Line for line the same
  parameters, `lam`, `ordλ`, `succλ`, `X`, `X⊆L`, `∅∈λ`, the same
  `ASt`, `H`, `M`, `C`. Resolves.
- Predecessors: `agents/tasks/LJ-1-462/Probe462.agda:101` (`feed`),
  `:109-111` (`lset-code`, unbuilt), `:133-134` (`step1`), `:136-138`
  (`HullClosedLset` as a type), `:140-142` (`πCommuteLset`, unbuilt);
  `agents/tasks/LJ-1-474/Probe474.agda:124-125` (`lset-codes`) and
  `:130-131` (`feed`); `agents/tasks/LJ-1-474/lj-1.474-report.md:70`
  (`## VERDICT`) and `:72-75` (the GO quote, verbatim);
  `agents/tasks/LJ-1-477/lj-1.477-report.md:97` (`## VERDICT`, NO-GO
  at `:99`); `agents/tasks/LJ-1-458/lj-1.458-report.md:80-84` and
  `agents/tasks/LJ-1-458/Probe458.agda:69-73` (`LsetAt-out-brief`,
  unbuilt). All resolve.
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:241`:
  `             → (δ : S) → ⟨ δ ∈ˢ M ⟩ → IsOrd δ → ⟨ Lset δ ∈ˢ M ⟩`.
  The archived companion carries `IsOrd` as a hypothesis, as the return
  says.
- The probe's own line cites: `:40` (`open hPropStructure 𝒮ʟ`),
  `:50-54` (`pins`), `:60-64` (`pins-no-ord`), `:79` (`VS`), `:103-104`
  (`hull-ord`), `:109-111` (`HullClosedLset`). All resolve.
- The numbers. I recomputed every figure from the `.time` files. W3
  rechecks: 1.86, 1.81, 1.82 seconds, median 1.82; RSS 385368064,
  385400832, 385384448 bytes, median 385384448. Full rechecks: 2.50,
  2.76, 2.55 seconds, median 2.55; RSS median 480165888 bytes. The
  excluded first runs, `w3-0` at 2.23 seconds and `full-0` at 2.69
  seconds, are reported as excluded and match their files. The report
  counts 49 non-blank non-comment lines in 111 total. I measure the
  same. `runs/full-ambiguous.out:2-8` holds the
  `[AmbiguousOverloadedProjection]` error the return names. The
  predecessor's own ARCHIVE and LITERATURE quotes also resolve; I
  opened all ten.
- The working tree. `git status --porcelain` shows only
  `?? agents/tasks/LJ-1-479/`. Nothing in `src/` changed, nothing
  committed, as the return states.

The single item that does not resolve is the one the BRIEF named and
the tree does not hold: the LJ-1.479 record in
`dev/pod/transitions/`. I report it above. It is not a claim the
return made, and the facts that do resolve corroborate the return.

## QUESTION 3: IS THE ENUMERATION COMPLETE

The return enumerates four live sources of `IsOrd` from membership or
satisfaction: `mem-ord`, `ω-mem-ord`, `isOrdAt-out`, `β-ord`. I ran my
own search over live `src/`, `grep -rn "→ IsOrd" src/`, and read every
hit: `src/L/Hierarchy.lagda.md:191`, `:274`, `:301`, `:334`, `:382`,
`:537`, `:621`; `src/L/Ordinal.lagda.md:221`, `:258`; the hypothesis
positions in `src/L/Ordinal/Stages.lagda.md`, `src/L/Ordinal/Linear.lagda.md`,
`src/L/Ordinal/SquareLaw.lagda.md`, `src/L/Axioms/Basic.lagda.md`; and
`src/L/BoundedSubset.lagda.md:813`, `:939`. Every conclusion of `IsOrd`
takes its ordinality as a hypothesis or from membership in a set that
is already ordinal. `src/L/Hull.lagda.md` uses `IsOrd` only as module
parameters, at `:148`, `:437`, `:522`. No lemma in live `src/`
concludes `IsOrd` from `⟨ y ∈ˢ M ⟩`. The enumeration is complete.

My attack found two additions. Both strengthen the NO-GO. Neither
overturns it.

First addition. The return enumerates only the OUT direction of the
graph formula, `Lset-only`. The IN direction spends the same
hypothesis. `graph-table` at `src/L/Hierarchy.lagda.md:382` reads
`  graph-table : (h : S) → IsOrd (fst (lookup b γ))`. So even a
putative cure that puts `Lset y` IN as the witness, rather than
reading a witness OUT, needs `IsOrd` on the same slot. Both directions
of the graph route are closed at a hull member. The return's NO-GO is
understated by one direction, and the understatement is in the safe
direction.

Second addition. The return says `hull-ord` is well-formed and
unbuilt, and that `IsOrd` has no source at a hull member. The stronger
fact is that no such source can exist at the consumer's hull. The live
consumer instantiates `HullStage` at `src/L/BoundedSubset.lagda.md:1405`:
`    module HS = HullStage lam ordλ succλ UK.X UK.X⊆Lλ UK.∅∈λ`. There
`UK.X = Lset α ∪ ⁅ x ⁆s` at `src/L/BoundedSubset.lagda.md:1150`, and
`Lα∈X` at `src/L/BoundedSubset.lagda.md:1161` puts every member of
`Lset α` into `X`:
`  Lα∈X : (z : S) → ⟨ z ∈ˢ Lset α ⟩ → ⟨ z ∈ˢ X ⟩`. Every `X` member
enters the hull as a base code: `val (base m) = emb m` at
`src/L/Hull.lagda.md:89` and `inHull` at `:117`. `IsOrd` at
`src/L/Constructible.lagda.md:142` demands every member transitive.
A level `Lset α` at a non-finite `α`, and `α∉ω` is a hypothesis of
`UnionKit` at `src/L/BoundedSubset.lagda.md:1147`, carries pairs:
`mkPair` at `src/L/Axioms/Basic.lagda.md:621-627` builds `⁅ fst a , fst b ⁆`
in `Lset σ` from members of `Lset σ`. A pair such as the singleton of
a numeral is not transitive, so it is not `IsOrd`, and it is a hull
member. This is a reading from delivered lemmas, each cited. I did not
build the refutation, and the return's discipline of calling the
obstruction a non-refutation stays correct for `HullClosedLset`
itself. But the next brief must not order a search for an `IsOrd`
source at this hull. At the consumer instantiation there is none to
find. The remaining honest options are the `IsOrd`-carrying
restatement, the shape the archived `level-in` already has at
`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:240-241`,
or a different route to step 2.

On the brief as cause. The brief mandated the `IsOrd`-free type and
forbade the hypothesis, at `agents/tasks/LJ-1-479/LJ-1.479.md:83`:
`**DO NOT POSTULATE AND DO NOT ADD AN ORDINALITY HYPOTHESIS ON `y`.** The hull`.
It also pre-priced this stop, at `agents/tasks/LJ-1-479/LJ-1.479.md:106`:
`cheapest point.`. A brief that forbids the cure and pre-authorizes
the stop can be said to have caused the outcome, so I checked whether
the forbidden cure was a real one. It was not. The four-step plan
consumes step 2 at the `y` that step 1 yields, `Probe462.agda:130-131`,
a hull member that carries no ordinality, and my second addition shows
the hypothesis cannot be paid at this hull at all. The brief did not
foreclose a true statement. It priced a route whose obstruction is
real. The return also names the one gap that stays open even with
`IsOrd` in hand: the meeting of `Lset-only` at the class carrier with
`wit`'s satisfaction at the stage, `src/L/Hierarchy.lagda.md:73`
against `src/L/Hull.lagda.md:323`. That enumeration item is present
and correct.

The four-step enumeration, `WHAT LEVELIN STILL OWES`, is faithful:
step 1 built with the term at `Probe462.agda:133-134`; step 2 this
task's NO-GO with the type at `Probe479.agda:109-111`; step 3 codes
built at `Probe474.agda:124-125` with the value equation `lset-code`
unbuilt at `Probe462.agda:109-111`; step 4 the critic-upheld NO-GO at
`agents/tasks/LJ-1-477/lj-1.477-report.md:97-99`. The companion
`πCommuteLset` and the hypotheses `levelIn` and `cover` are all named
with their sites. Nothing in the plan is dropped.

## VERDICT

**Upheld.** The verdict line matches the body. Every load-bearing
claim resolves at `file:line` today, and the one non-resolving record
was named by the brief, not claimed by the return. The enumeration is
complete, and my two additions, the IN direction `graph-table` at
`src/L/Hierarchy.lagda.md:382` spending the same `IsOrd`, and the
impossibility of an `IsOrd` source at the consumer's hull, both
strengthen the NO-GO. The uniqueness obstruction is real, it is
measured, and the return stopped at the cheapest point exactly as its
brief priced. The obligation `HullClosedLset` stays open. With this
file and exit 0, row `sys-critic-upheld-no-go` closes the task.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. It is the retired per-episode journal. This
  review measures a live-tree NO-GO whose history is the task
  directory.
- `archive/dev/ORCHESTRATION.md`: not read, declined. Retired
  orchestration record. No orchestration question is at issue.
- `archive/dev/DD-archived.md`: read at `:1`. Quote:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined,
  not used. The clauses that bind this slot came in the standing
  instruction, not from the archive.
- `archive/dev/PLAN-archived.md`: not read, declined. Retired plan.
  The live plan is the four steps at `Probe462.agda`.
- `dev/ARCHIVE.md`: read at `:29`. Quote:
  `- **Module.** The module's name as it was known in the live tree, e.g.`.
  Declined, not used. No module was retired by LJ-1.479, so no row was
  owed.

One archived file outside the candidates was used:
`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:241`, quoted
in Question 3, for the shape of the `IsOrd`-carrying restatement.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:96`. Quote:
  `> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`. Used. Devlin's
  biconditional pins `v = L_γ` at an ORDINAL index `γ`. The tree's
  analogue is `Lset-only` and it spends `IsOrd` on that same index
  slot. The literature agrees with the return: the graph determines
  its value at an ordinal, and the hull member `y` is not one.
- `dev/literature/BIBLIOGRAPHY.md`: not read, declined. No source
  beyond Devlin II.5 was needed for this review.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is at issue.
- `dev/literature/geology.md`: not read, declined. Stratigraphy of the
  literature corpus. Not relevant to a uniqueness obstruction.
- `dev/literature/devlin-errata.md`: not read, declined. The lemma I
  used, Devlin II.5 by 2.7, is not on the errata path I needed, and
  the return cites no Devlin lemma whose correction would change the
  NO-GO.
