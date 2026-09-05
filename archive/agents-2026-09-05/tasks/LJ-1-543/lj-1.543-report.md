# LJ-1.543 report: B6 is the cheap reading, and it is 9 lines

## HEAD
head_slot: coder
machine: shared
verdict: GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-543/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event: peak footprint 222,200,552 bytes, about 212 MiB,
against an 8 GB cap (`runs/final-8.out`). Nothing is postulated, the file
carries `--safe`, and there is no hole. The probe is a raw `.agda` file, so it
carries no ` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot
fire on it.

**GATES RUN.** `lint-prose`, `lint-agda`, `weave-i18n --check`, `check-glossary`,
`ledger --check`, `check-probes`, `check-closure`, `check-fences`,
`check-rule-ids` and `check-spec-surface`: all exit 0. I did NOT run
`make typecheck`. `git status --porcelain` shows one entry, the untracked
`agents/tasks/LJ-1-543/`, so no master changed and a whole-tree typecheck would
measure nothing about this task. The worktree carries no `.venv`, so every gate
ran as `/Users/alsg/Agentic/Bedrock/.venv/bin/python`, the pinned interpreter of
the main checkout, with the working directory left in this worktree.

## VERDICT

**GO. `SubsetIntoStage` IS INHABITED** at `[LJ-1.523]`'s type, letter for
letter, at `agents/tasks/LJ-1-543/Probe543.agda:125-130`. The obligation witness
agrees: `scripts/pod/witness.py` reports
`pass exit=0 agents/tasks/LJ-1-543/Probe543.agda::SubsetIntoStage`.

| runs | what the file was | result |
|---|---|---|
| `runs/w3-1.out` | the W3 slice ALONE, before `mem-ord`'s implicit was given | exit 42, `[UnsolvedMetaVariables]` |
| `runs/w3-2.out` to `runs/w3-4.out` | the W3 slice ALONE, kept at `runs/w3-slice.agda.txt` | exit 0, 0.96 to 0.97 s |
| `runs/full-1.out` | sections 1 to 4 added, before `L.Ordinal.Stages` was imported | exit 42, `[NotInScope]` |
| `runs/full-2.out` | the same with that import | exit 0 |
| `runs/final-1.out` to `runs/final-3.out` | the same, 162 lines, before section 4.4 | exit 0 |
| `runs/final-4.out` to `runs/final-6.out` | 178 lines, before four cited line numbers were corrected in the comments | exit 0 |
| `runs/fresh-1.out` | section 4.4 added | exit 0 |
| `runs/final-7.out` to `runs/final-9.out` | **the file exactly as this report describes it**, 178 lines | exit 0, 0.99 to 1.01 s |
| `runs/skip-1.out`, `runs/skip-2.out` | the same file NOT deleted first, so Agda skips it | exit 0, 0.86 to 0.87 s, and no "Checking" line |

Every run except the two `skip-*` runs deleted
`_build/2.8.0/agda/agents/tasks/LJ-1-543/Probe543.agdai` first, because Agda
skips a file whose content is unchanged and a run that skips measures nothing.
The two `skip-*` runs are used once, as the interface-load baseline, and
nowhere else.

**NO `InjCode` AND NO `Formula` ENTER THE FILE.** The conclusion is the bare
ambient membership `⟨ z ∈ˢ Lset (fst κ) ⟩` at the V-carrier. Neither closed
route of `[LJ-1.533]` and `[LJ-1.535]` is entered, so the coding wall is not
touched. `[LJ-1.540]`'s split is confirmed at the type level and now also at the
proof level.

## CHEAP OR THE THEOREM

**REQUIRED SECTION. IT IS THE CHEAP READING, AND THE ROW COSTS 9 LINES.**

`z` is an ORDINAL BELOW `κ`, and the tower places every such `z` with no
theorem. The measured chain is three named facts and nothing else:

1. `y ∈ˢ 𝒫 κ` is `y ⊆ˢ κ`, because `𝒫 a = ℩ (hasPower a)`
   (`src/FOL/ZFModel.lagda.md:287-288`) and `hasPower` realizes the class
   `λ x → x ⊆ˢ a` (`src/FOL/ZFModel.lagda.md:199`). One projection,
   `℩-spec` (`src/FOL/ZFModel.lagda.md:123-124`).
2. `z ∈ y ⊆ κ` gives `z ∈ˢ fst κ`, once `z` is known constructible. It is,
   by `isL-trans` (`src/L/Constructible.lagda.md:379`).
3. `z ∈ κ` with `IsOrd (fst κ)` gives `IsOrd z` by `mem-ord`
   (`src/L/Ordinal.lagda.md:221`), and then
   `Lset-cumul` (`src/L/Ordinal/Stages.lagda.md:164-165`) applied to
   `ord∈Lset-suc` (`src/L/Ordinal/Stages.lagda.md:434`) lands it in
   `Lset (fst κ)`.

**THE LINE COUNT THE BRIEF ASKED FOR, MEASURED AND NOT ESTIMATED.** Clause W4
asks for the ideal form written fresh, and section 4.4
(`agents/tasks/LJ-1-543/Probe543.agda:169-178`) is that form: the same proof
with every intermediate name inlined, in ONE declaration.
**It is 9 non-blank non-comment lines.** With its type
(`SubsetIntoStageAt`, `agents/tasks/LJ-1-543/Probe543.agda:119-123`, 5 lines)
the whole row is 14. The brief estimated about 35 lines for the obligation and
about 140 for the probe. **The obligation is 9 and the probe is 70.**

**WHY IT IS NOT THE BOUNDED SUBSET THEOREM, SAID AT `file:line`.** The theorem's
conclusion is `theorem : ⟨ x ∈ˢ Lset κ ⟩` (`src/L/BoundedSubset.lagda.md:1621`),
and its `x` is the SUBSET: `x⊆Lα` binds it as a subset of `Lset α` for an
`α ∈ κ` (`src/L/BoundedSubset.lagda.md:1391`). B6's `z` is one level lower, a
MEMBER of a subset of `κ`, so its rank is fixed by itself and the theorem has
nothing to do. **The brief's own suspicion is the right one and I confirm it by
the elaborator, not by a sentence: `L.BoundedSubset` is not in the import list
of `agents/tasks/LJ-1-543/Probe543.agda:17-23`**, so neither
`Devlin55.BoundedSubsetAt` (`src/L/BoundedSubset.lagda.md:1385-1395`) nor its
`levelIn` and `cover` (`src/L/BoundedSubset.lagda.md:1555-1557`) can be behind
any line of the term. `IsCardinal` does not appear either.

**SO `levelIn` AND `cover` STAY OFF THIS BRIDGE'S BILL**, and `[LJ-1.523]`'s
record of them as Π arguments of `BoundedSubsetTheorem` is untouched by this
task. I did not discharge them and I did not carry them.

## D-10, BEFORE ANY AGDA

**THE QUESTION.** "Say at `file:line` what `z ∈ y ∈ 𝒫 κ` gives you about `z`. If
it makes `z` an ordinal below `κ`, name the tower lemma that places it."

**THE ANSWER: IT MAKES `z` AN ORDINAL BELOW `κ`, AND THE TOWER LEMMA IS
`Lset-cumul`.**

The reading turns on one thing the brief did not name, and it is the reason W3
was worth its own slice. **`⊆ˢ` is the INTERNAL subset relation.**
`a ⊆ˢ b = ⋀ S (λ x → (x ∈ˢ a) ⇒ (x ∈ˢ b))` (`src/FOL/ZFModel.lagda.md:141-142`),
and at `𝒮ʟ` that `S` is `SL.S`, so the power-set hypothesis quantifies over
CONSTRUCTIBLE members of `y` only. **B6 hands `z` in AMBIENT**
(`agents/tasks/LJ-1-523/Probe523.agda:227` binds `z : SV.S`), so the hypothesis
does not apply to it until `z` is known constructible. That is the one step of
the row that is not a projection, and it is `isL-trans`
(`src/L/Constructible.lagda.md:379`): `z ∈ y` and `y` in `L` give `z` in `L`.

After that step the row is arithmetic on ordinals. `mem-ord`
(`src/L/Ordinal.lagda.md:221`) makes `z` an ordinal, `ord∈Lset-suc`
(`src/L/Ordinal/Stages.lagda.md:434`) puts it in the stage after itself, and
`Lset-cumul` (`src/L/Ordinal/Stages.lagda.md:164-165`) carries it to
`Lset (fst κ)`.

**AND THE MEMBERSHIP DOES NOT LIFT TO `y` ITSELF.** The same three lemmas say
nothing about `⟨ fst y ∈ˢ Lset (fst κ) ⟩`, because `y` is a subset of `κ` and
not a member of it, so `mem-ord` does not reach it and `Lset-cumul` has no
`y ∈ˢ fst κ` to consume. **That statement is the bounded subset theorem, and it
is a different row.** I did not build it and I make no claim about its price.

## W3, AND IT RAN FIRST

**THE QUESTION.** "`z`, from `z ∈ y` and `y ∈ 𝒫 κ`, at its strongest delivered
characterisation."

**THE ANSWER, AS A TYPECHECKED TERM AND NOT A SENTENCE.** `zStrongest`
(`agents/tasks/LJ-1-543/Probe543.agda:57-62`) is
`⟨ isL z ⟩ × ⟨ z ∈ˢ fst κ ⟩ × IsOrd z`, and `z-strongest`
(`agents/tasks/LJ-1-543/Probe543.agda:64-82`) inhabits it. **`z` is a
constructible ordinal, and it is a member of `fst κ`.** All three conjuncts come
out of the two hypotheses with no extra input.

**COST OF W3.** The slice was typechecked ALONE first, before sections 2 to 4
existed. It is kept at `runs/w3-slice.agda.txt` and its green runs are
`runs/w3-2.out` to `runs/w3-4.out`: 0.97 s, 0.97 s and 0.96 s, exit 0 each. The
brief estimated about 15 lines and under 30 seconds.
**Measured: 16 non-blank non-comment lines and under 1 s.** The line estimate
was accurate. The brief also said not to fund W3 against `[LJ-1.540]`'s numbers,
and nothing here is.

**ONE ATTEMPT WAS RED AND THE REASON IS WORTH THE NEXT BRIEF'S TIME.**
`runs/w3-1.out` is exit 42, `[UnsolvedMetaVariables]` at `mem-ord`'s implicit
`A`. **`IsOrd` is a definition and not a constructor**
(`IsOrd A = isTransV A × ...`, `src/L/Constructible.lagda.md:141-142`), so Agda
cannot invert `IsOrd _A =?= IsOrd (fst κ)` and the argument must be given as
`mem-ord {A = fst κ}`. This costs one word and it will cost the same word at
every later use of `mem-ord` against a projected ordinal.

## WHAT THE ROW DOES NOT NEED, MEASURED BY THE ELABORATOR

Three surplus measurements, in the style `[LJ-1.540]` used for `x⊆Lα`. Each is a
term in the file, so each is checked and not claimed.

1. **THE MODEL IS SURPLUS, EXCEPT FOR ONE PROJECTION.**
   `subset-is-all-the-power-set-gives`
   (`agents/tasks/LJ-1-543/Probe543.agda:141-145`) is the row with
   `⟨ fst y ∈ˢ fst (𝒫 κ) ⟩` replaced by `⟨ y ModelL.⊆ˢ κ ⟩`, and `isZFModel`
   leaves the statement entirely. **So B6 consumes `℩-spec` at `hasPower` and
   no axiom of the model.**
2. **AND THE L-CARRIER IS SURPLUS TOO, ONCE THE SUBSET FACT IS AMBIENT.**
   `no-L-side-left` (`agents/tasks/LJ-1-543/Probe543.agda:152-156`) is the row
   at the V-carrier throughout: no `SL.S`, no `isL`, no model.
   **It is 1 line.** The only work `y` does in the real row is to carry
   `⟨ isL (fst y) ⟩` into the internal quantifier of `⊆ˢ`.
3. **THE MATHEMATICS IS `ord-below-lands`
   (`agents/tasks/LJ-1-543/Probe543.agda:100-106`), 7 lines**, and it is a
   statement about V and the stage function with no L-model in it at all:
   `(κ : SV.S) → IsOrd κ → (z : SV.S) → ⟨ z ∈ˢ κ ⟩ → ⟨ z ∈ˢ Lset κ ⟩`.
   Everything else in the row is plumbing between the model's power set and the
   ambient membership.

**NO HYPOTHESIS OF THE OBLIGATION IS SURPLUS.** All six binders of
`SubsetIntoStage` are used. This is the opposite of `[LJ-1.540]`'s finding at
B7, where the fourth hypothesis was bound and never read.

## WHAT B8 WANTS

Required section, three sentences, and **I did not build it.**

`LimitAbove` (`agents/tasks/LJ-1-523/Probe523.agda:244-251`) asks, for an
ordinal `α` and a constructible `x`, for a truncated ordinal `lam` that is above
`α`, closed under `sucV`, and whose stage already holds `x`: four conjuncts, of
which three are about `lam` alone and one relates `lam` to `x`.
**This task's method does NOT reach it**, because B6 is handed its `κ` and only
looks `z` up in the tower, while B8 must CONSTRUCT an ordinal, and neither
`Lset-cumul` nor `ord∈Lset-suc` builds one.
The machinery that looks closest is `Ladder`
(`src/L/Reflect.lagda.md:256`), whose `top` (`:268`), `top-ord` (`:271`) and
`G∈top` (`:274`) are an ω-indexed union with its ordinality and its rungs
inside it, which answers the first two conjuncts if the rungs are chosen to
start above both `α` and a stage of `x`; **I did not typecheck that fit, and the
successor-closure conjunct and `⟨ x ∈ˢ Lset lam ⟩` are not in that module, so
this is a reading of the source and not a price.**

## THE NUMBERS

| item | estimate | measured |
|---|---|---|
| probe, total | about 140 lines | 178 lines, 154 non-blank, 70 non-blank non-comment |
| the obligation `SubsetIntoStage` alone | about 35 lines | 6 non-comment (`agents/tasks/LJ-1-543/Probe543.agda:125-130`) |
| the row WRITTEN FRESH, one declaration | not estimated | **9 non-comment** (`agents/tasks/LJ-1-543/Probe543.agda:169-178`) |
| the row's TYPE, `[LJ-1.523]`'s letter for letter | not estimated | 5 non-comment (`agents/tasks/LJ-1-543/Probe543.agda:119-123`) |
| the mathematics alone, `ord-below-lands` | not estimated | 7 non-comment (`agents/tasks/LJ-1-543/Probe543.agda:100-106`) |
| the row with every L-side term gone | not estimated | 1 non-comment (`agents/tasks/LJ-1-543/Probe543.agda:156`) |
| W3 | about 15 lines, under 30 s | 16 non-comment; 0.97, 0.97, 0.96 s (`runs/w3-2.out` to `runs/w3-4.out`) |
| typecheck, whole probe | not estimated | 0.99, 1.00 and 1.01 s (`runs/final-7.out` to `runs/final-9.out`) |
| interface-load baseline, same file skipped | not estimated | 0.86 and 0.87 s (`runs/skip-1.out`, `runs/skip-2.out`) |
| elaboration of the whole probe | not estimated | **NOT RESOLVED AT THIS SCALE. Between about 0.05 s and 0.15 s**, and the paragraph below says why |
| peak footprint | not estimated | 222,200,552 bytes, about 212 MiB (`runs/final-8.out`) |
| attempts to green | not estimated | TWO red, both one-word fixes: `mem-ord`'s implicit `A` (`runs/w3-1.out`) and a missing import of `L.Ordinal.Stages` (`runs/full-1.out`) |

**THE ELABORATION FIGURE IS NOT A NUMBER AND I WILL NOT WRITE IT AS ONE.** I
measured the interface-load baseline twice on this task. The first pair, on the
same 178-line file before four cited line numbers were corrected in its
COMMENTS, read 0.94 and 0.95 s. The second pair, at
`runs/skip-1.out` and `runs/skip-2.out`, reads 0.86 and 0.87 s. A comment does
not change elaboration, so the 0.09 s between the pairs is machine noise, and it
is larger than the 0.13 s the second pair leaves for the whole probe.
**So the row's elaboration is smaller than this method can resolve, and the only
defensible statement is an upper bound of about 0.15 s.** A row that cannot be
timed against interface loading is not a row anyone should price.

**THE ESTIMATE WAS HIGH ON THE ROW AND HIGH ON THE PROBE, AND THE REASON IS THE
SAME ONE.** The brief priced B6 against `[LJ-1.540]`, which built an injection.
This row reads a membership, and a membership costs two library lemmas.
**The probe is 178 lines because the brief ordered W3 as a separate slice and
because I added four surplus measurements the brief did not ask for; the row
itself is 9 lines.** The typecheck figures are the probe alone with the tree's
interfaces warm. They are not a chapter price and must not be quoted as one.

**FOR THE MATHEMATICIAN: THIS BRIDGE HAS BEEN OVER-PRICED, AND THE MEASUREMENT
SAYS BY HOW MUCH AT ONE ROW.** B6 was carried as a row that might inherit
`levelIn` and `cover`. It inherits neither, and it is 9 lines.

## WHAT I DID NOT DO

- I did not land anything in `src/`. The tree is unchanged outside
  `agents/tasks/LJ-1-543/`.
- I did not build an `InjCode` and did not look for a `Formula`. The row is
  ambient and both coded routes are closed by `[LJ-1.533]` and `[LJ-1.535]`.
- I did not attempt B8 or B10, and I did not attempt B5 or B9. AD12 gives this
  brief one obligation.
- I did not discharge `levelIn` or `cover` and I did not carry them as
  hypotheses either, because the row does not want them.
- I did not postulate, and I left no hole.
- I did not set `GHCRTS`, and I ran one Agda process at a time.
- I did not write `review-of-SubsetIntoStage.md`. That file states a NO-GO and
  this is a GO.
- **I did not measure whether `y` itself lands in `Lset (fst κ)`.** That is the
  bounded subset theorem's statement, one level up, and this task says nothing
  about its price.
- **I did not price the LANDING of this row into `src/`.** The brief forbids a
  landing and I obeyed. What I can say is that the row imports only
  `L.Constructible`, `L.Ordinal`, `L.Ordinal.Stages` and `FOL.ZFModel`, so a
  landing site has a small import closure to check for cycles. I did not check
  it.
- I did not run `make typecheck` and I did not run `make check`, because no
  master changed.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED.** `:165` is
  "| LJ-1.90 | Instantiate BoundedSubsetAt for the first time | REACHES cardκ | Every other hypothesis takes a value, including AllCodes A in Lset lam. Nothing in the tree proves any set is a cardinal |".
  That is the record of what `BoundedSubsetAt` costs to instantiate, and it is
  why the D-10 question was worth asking before any Agda: if B6 had needed that
  module, the row would have reached `cardκ` and stopped. It does not reach it,
  and the import list is the evidence.
- `archive/dev/JOURNAL.md`: **DECLINED.** `:1` is "# ARCHIVED 2026-08-20". The
  per-episode journal is retired in favour of `agents/tasks/<CODE>/`, and both
  predecessors this task needed, `[LJ-1.523]` and `[LJ-1.540]`, are in those
  task directories. Not used.
- `archive/dev/JOURNAL-archived.md`: **DECLINED.** `:1` is
  "# Archived journal: the retired route". B6 is on the live route. Not used.
- `dev/ARCHIVE.md`: **DECLINED.** `:1` is "# ARCHIVE.md: the archive registry".
  It registers retired MODULES. This task retires none and lands nothing, so
  clause W4's move-to-archive half has no subject here. Not used.
- `archive/dev/DECISIONS-archived.md`: **DECLINED.** `:1` is
  "# Archived decisions: the D series". A bare `D<n>` is not a rule in force.
  Not used.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ AND USED, AND IT SETTLED THE
  CHEAP-OR-THE-THEOREM QUESTION FROM THE SOURCE SIDE.** `:346` is
  "8. The hierarchy basics 1.1: transitivity, monotonicity, L_α ∩ On = α,".
  The source files "L_α ∩ On = α" under HIERARCHY BASICS, not under the
  condensation lemma of 5.2. B6 is the easy inclusion of that equation, so the
  source agrees with the measurement: it is a tower fact and not the theorem.
  `:234` is
  "5. Ordinal bookkeeping: M ∩ On = β (transitivity of M, ordinals absolute),"
  and it is the same fact used inside the condensation argument, which is why
  the two rows look alike from a distance.
- `dev/literature/truncation-and-selection.md`: **DECLINED.** `:1` is
  "# Truncation and selection: how the two literatures pick a witness". This row
  selects no witness: its only truncation-shaped input is `⟨ isL (fst y) ⟩`, and
  `isL-trans` (`src/L/Constructible.lagda.md:379-383`) already eliminates it
  into an hProp inside the library. Not used.
- `dev/literature/digest.md`: **DECLINED.** `:1` is
  "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  B6 sits on the `Def` tower and no claim here turns on a rud fact. Not used.
- `dev/literature/terms-2026-08.md`: **DECLINED.** `:1` is
  "# The terminology dossier: fourteen renderings for the owner's ruling". This
  report names no new term and adds no glossary entry. Not used.
- `dev/literature/geology.md`: **DECLINED.** `:1` is
  "# Geology dossier: set-theoretic geology sources and the five questions".
  Set-theoretic geology is not on the `[LJ-1]` route and this row touches no
  ground model. Not used.
