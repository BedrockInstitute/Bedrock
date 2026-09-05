# LJ-1.395 report: the band recursion, and the one residue it leaves

slot: `coder`. Written early as a skeleton and filled as answers landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-395/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time, no heap event.

TARGET: build TWO terms in `agents/tasks/LJ-1-395/Probe395.agda`, at a GENERIC
band, with every case fed by a named supplier taken as a module hypothesis:

1. `band-owes`, the residue, bound by the brief's three clauses.
2. `sq-band`, the recursion, by `∈-induction`, matching `L.StageCardinal`'s
   module parameter exactly.

PREDECESSOR CLAUSE (owner 2026-08-20, audit F1 and F3). The type of a module
hypothesis is the type the predecessor typechecked, and the verdict is the
predecessor's report. `[LJ-1.393]` names `amb-init` FALSE
(`agents/tasks/LJ-1-393/lj-1.393-report.md:13-20`,
`agents/tasks/LJ-1-393/Probe393.agda:164-171`). I do not inhabit that type.
The type that typechecked is `amb-init'` (`Probe393.agda:207-210`).
`[LJ-1.394]` is GO on `descent-amb` and NO-GO on `not-ambcard-gives`; the
latter is the residue.

STATUS SKELETON (filled as runs land):

- [x] motive phase: `band-owes` and the motive green, three case holes, the
      only errors are the three holes. 2.03 s, `runs/motive-holes.out`.
- [x] full file green, median of three: 1.66 s. `runs/full-{1,2,3}.out`.
- [x] floor (empty module), median of three: 0.05 s. `runs/floor-{1,2,3}.out`.
- [x] witness meter, both obligations, grouped: PASS, exit 0, 1.61 s.
- [x] consumer match checked mechanically by `plugs-in`.
- [x] survey duty, ARCHIVE USED and LITERATURE USED, sections 11 and 12.

## VERDICT

**GO.** Both obligations typecheck (`agents/tasks/LJ-1-395/Probe395.agda`,
exit 0) and both PASS the program's own witness meter (`scripts/pod/witness.py`,
grouped run, exit 0, 1.61 s, 0 UNRESOLVED of 2). The recursion assembled with
the types the predecessors delivered, and the residue it leaves is ONE datum:
the untruncated ambient injection below a non-`AmbCard` site. That datum is
the campaign's next bill, and section 9 names it.

This return replaces the 2026-08-19 file that took the refuted `amb-init` as a
hypothesis. That combination is the hollow GO named at
`dev/pod/audit-2026-08-20.md:57-67` (F3). The present file does not inhabit
that type.

## 1. What was built

All in `agents/tasks/LJ-1-395/Probe395.agda`, module
`LJ-1-395.Probe395 {ℓ} (lem) (α₀) (oα₀) (amb-init') (descent-amb) (sq-suc)`:

- The supplier statements as module hypotheses, and nothing from an earlier
  probe is imported or copied. `amb-init'` is [LJ-1.393]'s CORRECTED type
  (`agents/tasks/LJ-1-393/Probe393.agda:207-210`) at
  `agents/tasks/LJ-1-395/Probe395.agda:56-70`. `descent-amb` is [LJ-1.394]'s
  TERM 1 (`agents/tasks/LJ-1-394/Probe394.agda:96-98`) at `:71-78`. `sq-suc`
  is [LJ-1.330]'s successor transfer
  (`agents/tasks/LJ-1-330/ProbeLJ1330A.agda:120-127`) at `:79-85`. All three
  are spelled with the tree's own notions UNFOLDED, because the named forms
  live in modules that take `lem` explicitly and cannot be opened above the
  header. This is [LJ-1.393]'s precedent
  (`agents/tasks/LJ-1-393/Probe393.agda:53-59`). Each pair is judgmentally
  equal, so the parameters carry the statements the reports give, with no
  adapter.
- `AmbCard` and `isPropAmbCard`: `:100-107`.
- `band-owes`, the residue: `:126-129`.
- `Goal`, the motive, and `inf-member`: `:140-144`.
- `step`, the cases: `:155-195`.
- `sq-band`, the obligation: `:201-204`.
- `band-ord`, `ConsumerShape` and `plugs-in`, the consumer match: `:210-222`.

**Why `sq-suc` is a third hypothesis, and why that is not a fourth case the
brief forbade.** The brief named `[LJ-1.393]`'s `amb-init`. That statement is
FALSE at `α := sucV ω` (`Probe393.agda:164-171`). The delivered repair
`amb-init'` needs `⟨ sucV ω ∈ α ⟩`. At an infinite ordinal that membership
fails exactly when `α ≡ sucV ω` (trichotomy, the branch `α ∈ sucV ω` dies by
`∈sucV-elim` against the infinitude). [LJ-1.330] already delivered the
successor transfer that closes that one site
(`ProbeLJ1330A.agda:120-127`, instantiated at ω at `:151-152`). [LJ-1.337]
used the same transfer as a case of this recursion
(`agents/tasks/LJ-1-337/ProbeLJ1337B.agda:103-109`). Taking the statement as
a hypothesis is assembly. Putting `sq (sucV ω)` in `band-owes` would name a
paid debt as unpaid, and would apply `sq` inside the residue. I did not
reprove `sq-suc`.

## 2. `band-owes`: the residue, and the three clauses

```agda
band-owes =
  (a : V ℓ) → IsOrd a → ⟨ ω ∈ a ⟩ → (AmbCard a → Empty.⊥)
  → Σ[ b ∈ V ℓ ] (IsOrd b × ⟨ b ∈ a ⟩ × ⟨ ω ∈ b ⟩ × (⟪ a ⟫ ↪ ⟪ b ⟫))
```

- **CLAUSE 1, CLOSED.** It is a `Type` (`:126`). Its `a` is its own binder.
  It takes no parameter of `sq-band`'s telescope.
- **CLAUSE 2, NO `sq` AT A BOUND VARIABLE.** The type does not contain the
  token `sq`, in either spelling, at any position.
- **CLAUSE 3, THE ONE LINE.** `band-owes` concludes an injection of the
  index of `a` into the index of a MEMBER of `a`, so no instance of it is a
  square law at any ordinal; its content is [LJ-1.394]'s `not-ambcard-gives`
  conclusion (`agents/tasks/LJ-1-394/Probe394.agda:251-256`), the statement
  that probe left as a NO-GO at its STEP 2.

The residue is exactly what the delivered cases do not spend. The `AmbCard`
case with `⟨ sucV ω ∈ x ⟩` is fed by `amb-init'`. The leftover `AmbCard`
site `x ≡ sucV ω` is fed by `sq-suc` at ω. The negative case is fed by
`descent-amb` only AFTER the data arrives, and the data is what the tree
cannot produce. Nothing else is owed: the base case is delivered
(`squareω`), the split is delivered (`lem` on a proposition), and the
induction is delivered (`∈-induction`).

## 3. The motive, and why it carries no band membership

The brief warns that the motive is where this recursion goes wrong, and that
it must carry the band membership and the infinitude down to every member.
Both delivered motives carry what their own consumers read: [LJ-1.390]'s
`Goal` carries `isL` (`agents/tasks/LJ-1-390/Probe390.agda:181`) because its
residue read it, and the chapter's `P` carries the band
(`src/L/StageCardinal.lagda.md:530-533`) because its branch read it
(`:545-546`). I read both before I wrote mine, as ordered.

My motive carries the ordinal certificate and the infinitude
(`agents/tasks/LJ-1-395/Probe395.agda:140-141`) and carries NO band
membership, because no supplier reads one at a member. The check the brief
names is that the induction hypothesis is usable at the descent step, and it
is used there: `membersq` consumes it at `:164-165`, with the certificate
produced by `mem-ord` (`src/L/Ordinal.lagda.md:221-222`) and the infinitude
by `inf-member` at `:143-144`, the chapter's own line
(`src/L/StageCardinal.lagda.md:559`). The band enters only at the top,
through `sq-band`'s third argument, and PART 5 is what spends it.

One consequence worth the channel's attention: `sq-band` does not read its
band argument (`:204`). The recursion runs at EVERY infinite ordinal, band
or not. The argument exists because the consumer's parameter carries it, and
`band-ord` spends it at the interface.

## 4. The classical step

The one classical step the brief names is the split by `lem` on `AmbCard x`
(`agents/tasks/LJ-1-395/Probe395.agda:162`), and it is clean: `AmbCard x` is
a proposition because it is a function into `Empty.⊥` (`:104-107`), so
`LEM (ℓ-suc ℓ)` decides it at the level it lives. As the brief anticipated,
this split is NOT the difficulty of the route.

A second `lem` sits on `sucV ω ∈ x` (`:168`). That is also clean: membership
is already an `hProp`, so the same `LEM (ℓ-suc ℓ)` decides it. It is not a
new principle. It is the extra hypothesis `amb-init'` added, decided rather
than assumed.

## 5. The consumer match, checked

**I checked the match, and the check is mechanical, not by eye.** The
consumer takes `sq` as a module parameter with no ordinal certificate
(`src/L/StageCardinal.lagda.md:17-20`). `plugs-in`
(`agents/tasks/LJ-1-395/Probe395.agda:221-222`) discharges that parameter at
`ConsumerShape` (`:215-219`), which repeats the chapter's stated type with
the same terms: `sucV` opened instead of qualified, and alpha-equivalent
binders. `sq δ` IS the Sigma the chapter writes
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`), judgmentally, so no transport
sits inside `plugs-in`, and `band-ord` (`:210-213`, the port of
`agents/tasks/LJ-1-390/Probe390.agda:208-211`) produces the certificate the
chapter does not ask for. So, once `band-owes` is paid, `plugs-in` closes
`L.StageCardinal`'s module parameter at exactly the stated type.

## 6. Runs, floor, slots

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched here.
One Agda process at a time, every dependency warm, from the repository root,
2026-08-20. Every run is recorded under `agents/tasks/LJ-1-395/runs/`:

- Motive phase, three holes, the only errors those three holes: 2.03 s,
  exit 42, `UnsolvedInteractionMetas` at `:152`, `:156`, `:157` of the
  holes file (those line numbers are the holes-file's; the filled file
  replaced them). `runs/motive-holes.out`.
- Full file, three consecutive runs: 1.86 s, 1.66 s, 1.52 s. Median
  **1.66 s**, exit 0 every time. `runs/full-{1,2,3}.out`.
- Empty-module floor, `Floor395.agda`, three consecutive runs: 0.05 s,
  0.05 s, 0.06 s. Median **0.05 s**. `runs/floor-{1,2,3}.out`.
- Witness meter, both obligations, grouped: PASS, exit 0, 1.61 s,
  0 UNRESOLVED of 2. `runs/witness.out`.

No run came near the heap cap. No `GHCRTS` was set by this return.

## 7. W2 and DD4

Everything is written once at a generic carrier. The module is generic in
`ℓ`; `α₀` and `oα₀` are the consumer's own parameters, copied as
`[LJ-1.390]` copied them (`agents/tasks/LJ-1-390/Probe390.agda:34-35`);
every obligation quantifies over a generic `x : V ℓ`. No band site is named
in either obligation's type, so nothing inherits [LJ-1.386]'s doubt about
`+ω ω` (`agents/tasks/LJ-1-386/lj-1.386-report.md:211-236`).

The step inspects `sucV ω ∈ x` because that is the extra hypothesis of
`amb-init'`. That is a delivered boundary of [LJ-1.393], not a band site.
The residue type does not name it.

## 8. W3: the motive probe

**GO.** The widest unmeasured term was whether one `∈-induction` motive
carries the ordinal certificate and the infinitude to every member without a
transport. The probe was the motive alone: `band-owes`, `Goal`, `inf-member`
and the induction call in place, all three case bodies holes
(`agents/tasks/LJ-1-395/runs/motive-holes.out`). The file's ONLY errors were
the three holes, so the motive carries, with no transport anywhere. Price of
that run: 2.03 s. The estimate was about 40 code lines for the two terms
together, against [LJ-1.390]'s 33-line comparable of shape, and the brief
forbids funding against it. Measured: the two obligations with their motive
and step are 50 code lines (`:126-129`, `:140-144`, `:155-195`, `:201-204`,
comments and blanks excluded). The extra against the 40 is the `sucV ω`
split that `amb-init'` forced. Do not fund against either number.

## 9. What GO earns, and the campaign's next bill

GO earns the square law at every band ordinal, conditional on `band-owes`,
and it earns the exact size of `band-owes`: ONE Sigma, the untruncated
ambient arrow at a non-`AmbCard` site. If `band-owes` is ever paid,
`plugs-in` closes `L.StageCardinal`'s module parameter at the stated type,
and with it the largest open item on the GCH route.

**The next bill is the untruncated ARROW at the negative sites.**
`band-owes` asks, at every `a` with `ω ∈ a` and `¬ AmbCard a`, for a member
`b ∈ a` with `ω ∈ b` and an injection `⟪ a ⟫ ↪ ⟪ b ⟫`, as data.
[LJ-1.394] measured that nothing in this tree produces it: `lem` does not
reach it, because the injection type is not a proposition, and `leastOf`
does not reach it, because the payload would not be a proposition
(`agents/tasks/LJ-1-394/review-of-not-ambcard-gives.md`, STEP 2). The
archived route carried the same item as its fourth: "the honest untruncated
transfer stays blocked"
(`agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:155-158`).
The residue states that debt as a type, at the recursion's own site.

Two more bills sit BEHIND the hypotheses, and the recursion does not owe
them: `amb-init'` rests on `amb-limit` in the repaired form [LJ-1.392]
delivered (`agents/tasks/LJ-1-392/lj-1.392-report.md:3-7`); and `AmbCard`
has no producer, exactly as `Init` had none before [LJ-1.393]. The recursion
needs neither: the split is by `lem` and not by a witness. `sq-suc` is
already delivered at [LJ-1.330]; it is not a bill.

## 10. What this task does NOT settle

- It does not pay `band-owes`. No square law at any ordinal is
  unconditional here.
- It does not produce `AmbCard` at any ordinal, and does not need to.
- It does not deliver `amb-limit`. The `amb-init'` hypothesis carries that
  demand, and the campaign still owes a site that discharges it.
- It does not inhabit the stated `amb-init`. That type is FALSE.

## 11. ARCHIVE USED

Each bullet names an injected path and quotes one line read at the cited
line.

- `archive/dev/JOURNAL-archived.md:1338`, read at the search hits: the
  journal records the cardinal step's pairing as "delivered CONDITIONAL on
  one named bound, the square law", and the supplier of that bound is what
  this probe assembles at the band. Nothing else in it bears on this task.
- `archive/dev/DECISIONS-archived.md:50`, D30's row, read for the craft
  clause W2 carries forward: the retiring chapters "state at abstract
  carriers and variable indices so nothing re-normalizes". This probe
  states every obligation at a generic band and a generic site.
- `archive/dev/TASKS-archived.md:82`, the archived task index: "Truncated
  square law at initial ordinals", DELIVERED, is the row of the route whose
  report the brief names as this task's map. Its Init form is the same
  supplier this recursion feeds in the AmbCard case, via `amb-init'`.
- `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:926`, the
  archived chapter itself: the least-of search "returns only the
  truncation", so at the non-initial ordinals the law stayed named. That
  named gap is this recursion's negative case, and the residue is the
  datum the archived route could not extract either.
- `dev/ARCHIVE.md:33`, read to resolve the injected candidate's own path:
  the registry rules that archive-src "carries one extra level, the
  ARCHIVAL EVENT", which is why the SquareLaw citation above carries its
  event directory. Nothing else in it was read for this task.

The task's own archive citation stands beside these: section 6 of
`agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:135-158`, read as the
brief ordered. Its four items are this recursion's cases in the archived
vocabulary: item 1 is the `AmbCard` case, item 2 is the descent, item 3 is
wiring this task does not touch, and item 4 is `band-owes`.

## 12. LITERATURE USED

- `dev/literature/truncation-and-selection.md:335`, the fact behind the
  residue's shape and behind [LJ-1.394]'s STEP 2 NO-GO: "A canonical
  injection needs a well-order on the INJECTIONS". This is why `band-owes`
  asks for the arrow as data and why `lem` cannot produce it.
- `dev/literature/digest.md:241`, the one pairing item a search finds: a
  "surjection g : α -> J_α^A when α is closed under Gödel pairing", the
  J-tower form of the closure this tree calls the square law. The digest
  offers no untruncated arrow, and this task consumed none of it.
- `dev/literature/terms-2026-08.md:290`, opened for the term's sense only:
  the square law is "The cardinal identity: the product of the members of
  an infinite" ordinal. No rendering question arises in a probe, and no
  glossary entry was written.
- `dev/literature/devlin-II5.md:1`, not used: "the Condensation Lemma and
  the GCH in L". This task assembles a recursion at a generic band, and no
  step of it consults a condensation argument. Opened at the head only.
- `dev/literature/geology.md:1`, not used: "set-theoretic geology sources
  and the five questions". Sources for the geology phase of a later
  milestone, and nothing in it bears on this probe. Opened at the head
  only.

## WHAT I DID NOT DO

- I did not import an earlier probe, and did not copy a proof from one. The
  three statements are parameters; the one ported term, `band-ord`, is 4
  lines from [LJ-1.390], and its provenance is stated at its site.
- I did not prove `Init`, build an injection out of anything, or rebuild any
  part of [LJ-1.392], [LJ-1.393] or [LJ-1.330]. No supplier was reproved.
- I did not inhabit the stated `amb-init`. The 2026-08-19 file in this
  directory did; this file replaced it.
- I did not touch `src/`, did not commit, did not push, and set no `GHCRTS`
  of my own.

## GATES RUN ON MY FILES

- `agda --safe agents/tasks/LJ-1-395/Probe395.agda`: exit 0, three
  consecutive recorded runs of the filled file. The motive-holes file:
  exit 42, three holes only. The floor file: exit 0, three consecutive
  runs.
- `scripts/pod/witness.py --code LJ-1.395 --brief
  agents/tasks/LJ-1-395/LJ-1.395.md`: both obligations PASS, grouped,
  exit 0 (`runs/witness.out`).
- `scripts/pod/check-survey-quotes.py LJ-1.395`: clean, 0 notes, 0 defects
  (`runs/survey.out`).
- `make check` was not run: it is the gate before a commit, and this slot
  never commits. The prose and Agda linters do not cover `agents/`
  (`scripts/gate/lint-agda.py:400`, `scripts/gate/lint-prose.py:457`), so
  no gate applies to these files beyond the ones above.

This worktree has no `.venv`. The witness and survey scripts were run with
`python3` (3.14.7). The Agda invocations did not go through Python.

## THE TREE AS I LEAVE IT

Written here, and nothing else touched:
`agents/tasks/LJ-1-395/Probe395.agda` (green, obligations metered; the
2026-08-19 hollow file that took refuted `amb-init` is replaced),
`agents/tasks/LJ-1-395/lj-1.395-report.md` (this report),
`agents/tasks/LJ-1-395/Floor395.agda` (the floor, unchanged),
`agents/tasks/LJ-1-395/runs/` (motive-holes, three full runs, three floor
runs, witness, survey). The tree outside this directory holds other tasks'
and the program's own in-flight files, none of them mine. Nothing
committed, nothing pushed.
