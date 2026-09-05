# Review of LJ-1.560#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld
attacked: agents/tasks/LJ-1-560/lj-1.560-report.md
brief: agents/tasks/LJ-1-560/LJ-1.560.md

## THE INVARIANT

The critic is not the author. The author ran as the `coder` slot. This
critic runs as `mathematician_adversarial`.

The predecessor's verdict is GO, not NO-GO. There is no
`review-of-search-bounds.md`. Row `sys-critic-upheld-no-go` does not
close this task. An agreed GO is still a real result.

`dev/pod/transitions/2026-08.jsonl` in this worktree carries no line
with `"task": "LJ-1.560"`. The file ends at seq 158, task `LJ-1.399`,
stamp 2026-08-19. Model and effort are therefore not on the record
here. The six facts come from the accept arm. The heads hash is on
`agents/tasks/LJ-1-560/.pod:1`.

## THE SIX FACTS OF THE INSTANCE

From `agents/tasks/LJ-1-560/runs/accept-1.out`:

- Probe560.agda rc 0, 0.87 s (`accept-1.out:16`)
- Red.agda rc 42, 0.77 s (`:17`)
- conjunct 1 FAILED; conjuncts 2 to 6 held (`:10-15`)
- exit 42, error class other, UnequalTerms (`:22-23`, `:24`)
- obligations delta -1, obligations open 0, probe not red
  (`:20`, `:24`, `obligations_probe_red: false`)
- heap wall false, in-fence lines 0, unbound_vacuous true (`:24`)
- 14 changed files, all under `agents/tasks/LJ-1-560/` (`:18`, `:24`)
- caliber `-A64m -I0 -M8g`, tier wide (`:5-6`)

`unbound_vacuous: true` here means conjunct 4 saw no `src/` master
change (`scripts/pod/accept.py:214-215`). It does not mean the
obligation name is missing. The obligation `search-bounds` stands at
`Probe560.agda:165-176`.

## QUESTION 1. DOES THE VERDICT LINE MATCH THE BODY

**Yes. The word is GO, and the body inhabits the obligation.**

The line is `agents/tasks/LJ-1-560/lj-1.560-report.md:3-4`:
`GO. THE OBLIGATION IS INHABITED, AND IT IS AN INSTANTIATION.`
`Probe560.agda:165-176`, exit 0.

The body carries each part of that line:

- The type `search-bounds` stands at `Probe560.agda:165-170`. The
  term is `Single.βω`, `Single.L.top-ord`, `Single.closed`,
  `Single.reflect`, `δ-∃∈` at `:171-176`.
- Those four `Single` names open at `src/L/Reflect.lagda.md:485-496`
  (`βω` at `:485-486`, `top-ord` via `module L = Ladder` at `:483`
  and `Ladder.top-ord` at `:271-272`, `closed` at `:492-493`,
  `reflect` at `:495-496`). `δ-∃∈` opens at
  `src/FOL/LevyHierarchy.lagda.md:57`.
- W3 was written first and typechecked alone: `runs/W3.agda`,
  `runs/w3-1.out` to `w3-3.out`, exit 0, 1.05 s / 0.95 s / 0.97 s
  (`w3-1.out:3`, `w3-2.out:2`, `w3-3.out:2`). The chapter already
  has the principle, so the task is an instantiation, as the brief
  ordered at `LJ-1.560.md:73-74` and `:114-115`.
- The stage is load-bearing. `runs/Red.agda:31-33` ascribes
  `Single.closed` at an arbitrary stage. `runs/red-1.out:3-18` is
  `UnequalTerms`, exit 42.

The accept arm's exit 42 does not flip the word. Conjunct 1 ran
`Red.agda` and stopped at the first failing target
(`scripts/pod/accept.py:165-166`). The body required that file to
fail (`lj-1.560-report.md:102-103`). The same arm records
Probe560.agda rc 0 and obligations delta -1. That is not the
unread-live-record defect `[LJ-1.375]` and `[LJ-1.376]` named. The
body names `red-1.out`.

One number in the line's neighbourhood does not match the cited
span. The report says "12 lines of type and 5 lines of term"
(`lj-1.560-report.md:8-9`). `Probe560.agda:165-176` is 12 lines in
total. The GO does not rest on that split. The brief estimated
about 170 lines (`LJ-1.560.md:101`). The inhabited term is three
library names and one constructor, as the body says at `:98-99`.
The brief told the worker to say the estimate was far too high if
the chapter already had the principle (`LJ-1.560.md:114-115`). The
worker said so.

The brief did not cause a false GO. It ordered an instantiation if
`src/L/Reflect.lagda.md` already proved a reflection principle
(`LJ-1.560.md:70-74`). The chapter does: `ClosedFor` at `:253-254`,
`Ladder.reflect` at `:411-412`, `Single.closed` at `:492-493`,
`Single.reflect` at `:495-496`.

No missed cure is required for the obligation the brief named.
`mkReflect` is re-ascribed at `Probe560.agda:99-103` and compared
with `Single` in the report table at `lj-1.560-report.md:46-50`.
The worker kept `Single` because the matrix stays untouched. The
obligation type does not ask for a prescribed ordinal inside the
stage. That choice is reasoned.

W3 named the unmeasured term and the probe. The coder wrote
`runs/W3.agda`. Amendment A21 is met. W2 is met: the mathematics
already lives at the generic carrier `Ladder` /
`Single` and this return instantiates it. W8 is met: the shape is
a theorem in the tree, not an axiom the tree fails.

## QUESTION 2. IS EVERY LOAD-BEARING CLAIM BACKED BY A FILE:LINE THAT RESOLVES TODAY

**No. The obligation claim resolves. Four supporting claims do
not resolve to the sentence they carry.**

Claims that resolve today:

- `ClosedFor` is the first conjunct of `search-bounds`, already
  named. `src/L/Reflect.lagda.md:253-254`:
  `ClosedFor β {k} ψ = (ρ : S ^ k) → Below β ρ → ⟨ SatEx ψ ρ ⟩ → ⟨ Wit ψ ρ β ⟩`.
  `satex-is-object` at `Probe560.agda:137-139` is `refl`.
- `Wit` cuts the search to `Lset σ`. `src/L/Reflect.lagda.md:164-165`.
- `pickStage` / `pickWitness` are the pointwise answer.
  `src/L/Reflect.lagda.md:183-184`, `:210-211`.
- `module Single` at `:442`. `Single.closed` at `:492-493`.
  `Single.reflect` at `:495-496`.
- `mkReflect` at `src/L/ReflectFo.lagda.md:525-530`.
- `Δ₀-relativize` at `src/FOL/Manipulation/Relativize.lagda.md:72`.
- `hasSeparationL` at `src/L/Axioms/Full.lagda.md:144-147`, and
  the `mkReflect` spend at `:151`.
- `mkBoundedFo` at `src/L/Axioms/Separation.lagda.md:449`.
- `separateΔ₀` at `:481-483`.
- `AtStage` wants `Δ₀` and `BoundedFo` at `:150` (`satBridge`)
  and `:163` (`carveSat`). Those lines resolve. They are a better
  cite than the brief's `:199-206`.
- `σ-∃` at `src/FOL/LevyHierarchy.lagda.md:75`.
- `ClosedFor` is not inherited by a larger stage.
  `src/L/ReflectFo.lagda.md:18-19` and `:498`.
- `Answers (∃̇ φ)` pays the single-matrix step.
  `src/L/ReflectFo.lagda.md:148`.
- `LsetS` keeps the first component as `Lset β`.
  `src/L/Axioms/Basic.lagda.md:160-161`.
- `wit-is-object` is `refl` at `Probe560.agda:130-133`. The
  identification is measured.
- The red control fails as recorded. `runs/red-1.out:3-18`.
- The first whole-probe run failed at the `ModelL` ascription.
  `runs/final-1.out:3-8`, `UnequalTerms` at then-line 215. The
  later runs exit 0 (`final-2.out:3`, `final-3.out:2`).
- Probe 225 lines, W3 81 lines: `wc` agrees.

Claims that do not resolve, or do not resolve to the claim:

1. **`defSet` line numbers.** The report at
   `lj-1.560-report.md:93-95` cites
   `src/L/Definability.lagda.md:106-107` for `smallSat` and
   `:108-109` for `defSet`. Today `:105` is `<!--/-->`, `:106` is
   blank, `:107` opens the fence, `smallSat` is `:108-109`, and
   `defSet` is `:111-112`. The brief had the `defSet` lines right
   (`LJ-1.560.md:30`). The probe comment at `Probe560.agda:154`
   has them right. The report does not.

2. **`Single.reflect` at `:520` in the W3 slice.**
   `runs/W3.agda:17` and `Probe560.agda:88` cite
   `src/L/Reflect.lagda.md:520` for `Single.reflect`. Today `:520`
   is recap prose: "at once, and gets everything above for it
   without rerunning any of it." The term is at `:495-496`. The
   report table at `lj-1.560-report.md:29` has `:495`. The probe
   comment does not.

3. **"The same inner satisfaction `defSet` reads."**
   `lj-1.560-report.md:93-94`. The probe's `_⊨_` is
   `FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`
   (`Probe560.agda:77-78`). That is inner satisfaction of the
   class `isL` (`src/FOL/Absoluteness.lagda.md:57-68`, `:77-78`).
   Quantifiers range over constructible sets.
   `defSet` reads `Formula ⟪ A ⟫ 1` under `𝒮ᵥ ↾ (∈ A)`:
   `src/L/Definability.lagda.md:14-16`, `smallSat` at `:108-109`.
   Quantifiers range over members of `A` only. Those are two
   structures. `AtStage.satBridge`
   (`src/L/Axioms/Separation.lagda.md:150-161`) is the bridge
   between them, not an identity. The report cites Definability
   as if the probe already sat on that bridge.

4. **"Nothing remains before `AtStage` would accept it."**
   `lj-1.560-report.md:59-64`. Two remainders stand in the
   worker's own type.
   - Grade. The third conjunct of `search-bounds` is
     `Δ₀ ψ → Δ₀ (boundAt ψ β oβ)` (`Probe560.agda:170`), filled
     by `δ-∃∈` (`:176`), which demands `Δ₀` of the matrix
     (`src/FOL/LevyHierarchy.lagda.md:57`). If `ψ` is not `Δ₀`,
     `AtStage.satBridge` refuses (`:150`).
   - Constants. `BoundedFo` of `∃̇∈ t φ` is
     `BoundedTm P t × BoundedFo P φ`
     (`src/FOL/Manipulation/Bounding.lagda.md:79`). For
     `boundAt`, `t` is `con (LsetS β oβ)`, so `BoundedTm`
     at stage `σ` is `⟨ Lset β ∈ Lset σ ⟩`
     (`Bounding.lagda.md:65`, `LsetS` at
     `src/L/Axioms/Basic.lagda.md:160-161`, `AtStage.Below` at
     `src/L/Axioms/Separation.lagda.md:129`). At `σ = β` that
     is `⟨ Lset β ∈ Lset β ⟩`. The `LsetS` reduction the
     report cites (`src/L/ReflectFo.lagda.md:88-96`) makes
     `Wit` and `boundAt` the same `Ω`. It does not put the
     bounding constant into its own stage.

The wrappers `separateΔ₀` and `hasSeparationL` do drop
hypotheses, and those re-ascriptions typecheck
(`Probe560.agda:208-225`). That does not make the `AtStage`
sentence true of `AtStage`.

## QUESTION 3. IS THE PREDECESSOR'S ENUMERATION COMPLETE

**The obligation is enumerated. The two blocked legs are not.**

Enumerated, and checked:

- Reflect already proves a reflection principle, not only
  `Ladder`. Title at `src/L/Reflect.lagda.md:1`, `ClosedFor` at
  `:253-254`, `Single` at `:442-496`.
- `mkReflect` is strictly stronger and relativizes the matrix
  (`src/L/ReflectFo.lagda.md:525-530`).
- `ClosedFor` does not merge across stages
  (`src/L/ReflectFo.lagda.md:18-19`, `:498`). A consumer that
  needs one stage for two formulas wants the joint ladder
  (`:148`).
- The red control shows the stage is not decoration.
- `final-1.out` is kept, not discarded.
- No `.venv` in this worktree, so `make check` was not run
  (`lj-1.560-report.md:180-186`).

Not enumerated, and load-bearing for the extra claims:

- The probe satisfies formulas in `L`, not in `(A, ∈)`. See
  question 2, claim 3. The brief's boundary is `defSet`
  (`LJ-1.560.md:77-80`). A `Formula S k` read by
  `Absoluteness.Single 𝒮ᵥ isL` is object language. It is not
  yet the object language `𝒟ₒ-intro` consumes
  (`src/L/Constructible.lagda.md:301-304` wants
  `Formula ⟪ A ⟫ 1` and `DefOf.defSet`).
- `[LJ-1.536]` measured `𝒟ₒ-intro` and `AtStage` at a Σ₁ graded
  formula (`agents/tasks/LJ-1-536/lj-1.536-report.md:3-5`,
  `:34-44`, `:56-70`). That NO-GO remains true of those two
  doors. `hasSeparationL` is `SetOf` in `L`
  (`src/L/Axioms/Full.lagda.md:144-147`), not `𝒟ₒ-intro`.
  `AtStage.carve∈𝒟ₒ` (`src/L/Axioms/Separation.lagda.md:198-199`)
  still wants `Δ₀`. The body says the 536 door "is open one
  level up" (`lj-1.560-report.md:122-124`). It does not
  instantiate `search-bounds` at `levelFo`. A measured cure
  does not transfer by analogy (`AGENTS.md:45`).
- `[LJ-1.557]` named a formula that would describe `leastOf` at
  `w` over the code predicate
  (`agents/tasks/LJ-1-557/lj-1.557-report.md:196-200`). The body
  says that obstruction "is exactly what section 3 removes"
  (`lj-1.560-report.md:126-132`). No term of this task is that
  formula. Section 3 bounds one outer `∃̇` of an arbitrary
  matrix. Whether the 557 predicate is of that shape is
  unmeasured here.
- Conjunct 1 of the accept arm failed because `runs/Red.agda`
  sits in write scope. The body records the red as required. It
  does not record that the harness will therefore report exit
  42 on a GO. That is a routing fact, not a mathematical one.
  It is still an unenumerated fact of this return.

The extra claims about the two legs do not flip the GO. The
obligation the brief named is `Probe560.agda::search-bounds`.
That term exists, it is a `Formula`, and it is an instantiation.
The next brief must re-measure at 536's door and at 557's
predicate. It must not fund either leg against this report's
section "WHAT THE TWO BLOCKED LEGS GET".

## ARCHIVE USED

- `archive/dev/JOURNAL.md`. **READ, NOT USED, DECLINED.** At
  `archive/dev/JOURNAL.md:10` the line reads
  "Nothing below is current."
  The file is the retired episode journal. It carries no
  measurement of `search-bounds` or of `L.Reflect`.
- `archive/dev/ORCHESTRATION.md`. **READ, NOT USED, DECLINED.**
  At `archive/dev/ORCHESTRATION.md:1` the line reads
  "# ORCHESTRATION: the orchestrator's operating rules"
  It is the archived process document. It carries no
  mathematics of reflection into a stage.
- `archive/dev/DD-archived.md`. **READ AND USED.** At
  `archive/dev/DD-archived.md:35` the line reads
  "The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed."
  Those four are the lens of this review. The three answers
  above are written from them. The predecessor's GO is a
  positive return. Question 1 of the four still applies: the
  GO is correct on its own inhabitation numbers.
- `archive/dev/PLAN-archived.md`. **READ, NOT USED, DECLINED.**
  At `archive/dev/PLAN-archived.md:1` the line reads
  "# ARCHIVED 2026-08-20"
  It is the archived construction registry. Nothing in it
  decides whether `Single.reflect` inhabits this obligation.
- `dev/ARCHIVE.md`. **READ, NOT USED, DECLINED.** At
  `dev/ARCHIVE.md:1` the line reads
  "# ARCHIVE.md: the archive registry"
  No retired module is this obligation. `src/L/Reflect.lagda.md`
  is live. This task retires nothing.

## LITERATURE USED

- `dev/literature/devlin-II5.md`. **READ AND USED.** At
  `dev/literature/devlin-II5.md:191` the line reads
  "reflects it down, so the witness z lies in X (`dev2.txt:1173-1183`)."
  That is Σ₁-elementarity at a quantifier-free matrix, with the
  witness landing in the smaller carrier. It confirms the
  classical shape of `search-bounds` for a Δ₀ matrix under one
  `∃̇`. It does not confirm the report's extra sentence that
  `AtStage` then accepts an arbitrary matrix. Devlin's step A
  names the quantifier-free restriction at
  `dev/literature/devlin-II5.md:193-194`.
- `dev/literature/BIBLIOGRAPHY.md`. **READ, NOT USED, DECLINED.**
  At `dev/literature/BIBLIOGRAPHY.md:1` the line reads
  "# Bibliography for the rud route"
  It is a source list. It states no II.5 theorem.
- `dev/literature/digest.md`. **READ, NOT USED, DECLINED.** At
  `dev/literature/digest.md:1` the line reads
  "# Digest: the orthodox form of the rud route, pinned from the collected literature"
  A search for "reflect" in this file returns no hit. The
  digest is the rud-route pin, not Montague reflection into a
  stage.
- `dev/literature/geology.md`. **READ, NOT USED, DECLINED.** At
  `dev/literature/geology.md:1` the line reads
  "# Geology dossier: set-theoretic geology sources and the five questions"
  Its "reflect" hits are geology (grounds, mantle), not a
  formula reflected into a stage of `L`.
- `dev/literature/devlin-errata.md`. **READ, NOT USED, DECLINED.**
  At `dev/literature/devlin-errata.md:1` the line reads
  "# Devlin errata: documented error classes (do-not-repeat checklist)"
  A search for "reflect" and for "II.5" returns no hit. No
  erratum in this file touches the shape `search-bounds` uses.
