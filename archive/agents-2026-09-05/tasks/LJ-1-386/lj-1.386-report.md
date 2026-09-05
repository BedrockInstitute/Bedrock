# LJ-1.386 report: internal existence of a pairing code at a band ordinal

slot: `mathematician`. Written incrementally (C-22). No commit, no push. I wrote
only in `agents/tasks/LJ-1-386/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M8g"`, one process, no heap event.

TARGET: state, at the band ordinal `+ω ω` (`src/L/Ordinal/StageArith.lagda.md:41-42`),
the proposition `∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁` for the `Good` of
`src/L/Cardinal.lagda.md:187-190`, then inhabit it or state the obstruction.

**AMENDED AT THE RETURN, 2026-08-19.** The acceptance run refused this return.
`agents/tasks/LJ-1-386/runs/accept-1.out` records conjunct 6 FAILED, because the
report carried no ARCHIVE USED section and no LITERATURE USED section. Sections
10 and 11 discharge that duty. **The probe, the runs and the verdict are
unchanged**, and I started no Agda process for the amendment. The survey was not
bookkeeping: it found ONE limit on section 4's door, and section 4 now carries it.

## VERDICT

**GO on the door, and the brief's target is REFUTED as a statement of leg 1.**

Three measurements, all green, all in `agents/tasks/LJ-1-386/Probe386.agda`,
exit 0:

1. **The proposition the brief names is INHABITED, and it is FREE.**
   `code-exists` at `:227-229` is the brief's statement verbatim at `+ω ω`.
   Its witness is the identity graph on the band ordinal. **The three
   conjuncts of that `Good` cost nothing at ANY `D` and at ANY site**
   (`good-from-placement`, `:203-205`), so the statement carries no cardinal
   arithmetic. **It is not leg 1.**
2. **The reason is in the type.** `Good` at `src/L/Cardinal.lagda.md:187-190`
   has three conjuncts, `svAt`, `domAt` and `injAt`. **It never names a
   target.** The clause that makes a coded injection descend is `InjCode`'s
   fourth conjunct at `src/L/Cardinal.lagda.md:228`, the value-in-`b` clause,
   and `Good` drops it. A statement that never mentions the target cannot say
   the square goes INTO the band ordinal.
3. **The door the route claimed IS real, and it is now measured.**
   `code-untruncates` at `:264-268`: a code that MERELY EXISTS gives an
   ambient injection AS DATA, `⟪ fst a ⟫ ↪ ⟪ fst b ⟫`, with no choice
   principle. `leastOf` under `lem` does the untruncation and `Small` reads
   the chosen code out. **That is the second door `[LJ-1.384]` said nobody had
   aimed at, and it holds.** **IT IS AN INJECTION AND NOTHING WIDER.** The two
   walls the archive records are a canonical BIJECTION
   (`archive/src/2026-08-09-rud-route/Everything.lagda.md:307-308`) and the
   untruncated EQUIVALENCE (`archive/dev/JOURNAL-archived.md:1732`). **This door
   moves neither**, and section 10 quotes both.

**So `[LJ-1.375]` section 3.4's INFERRED sentence is now a measurement, and it
is FALSE.** The read-out of a coded injection is not「the same untruncation」:
`code-untruncates` takes the truncated hypothesis and returns data.

**What is still unbuilt is narrower and better named than before.** It is not
「internal existence」in general. It is exactly two objects, and section 3
states both.

## 1. THE STATEMENT, AS THE TREE TAKES IT

`Canonical` at `src/L/Cardinal.lagda.md:182-204` takes two parameters, `a` and
`D`. `a` fixes the search stage through `SiteBound a` (`:163-172`), and `D` is
the domain of the coded function. `Good A` is then three satisfactions at the
environment `(up A ∷ D ∷ [])`.

Two facts follow from the type alone, and both are checkable at those lines:

- **`Good` has no third parameter.** No ordinal, no cardinal and no target
  occurs in it. The predicate is「`A` codes an injective function with domain
  exactly `D`」and nothing else.
- **`Canonical` has ZERO consumers in `src/` today. MEASURED**:
  `grep -rn "Canonical" src/` returns one hit outside `src/Base/Classical.lagda.md`,
  which is its own definition line. The homonym at `src/Base/Classical.lagda.md:119`
  is a different module. So no delivered chapter fixes what `a` and `D` are
  meant to be, and the brief's reading of them is an interpretation, not a
  reading.

## 2. THE MEASUREMENT: THE NAMED PROPOSITION IS FREE

`module IdGraph (D : S)` at `Probe386.agda:94` builds, for EVERY L-element `D`,
the set `{ ⟨x,x⟩ : x ∈ D }`, by `hasReplacementL` on the formula `y = ⟨x,x⟩`.
It then discharges all FOUR `InjCode` conjuncts at source `D` and target `D`:

| conjunct | term | line |
|---|---|---:|
| `svAt` | `sv` | `Probe386.agda:143` |
| `injAt` | `ij` | `Probe386.agda:154` |
| `domAt` | `dm` | `Probe386.agda:165` |
| value-in-`b` | `ran` | `Probe386.agda:180` |
| the four together | `idCode : InjCode G D D` | `Probe386.agda:186-187` |

`good-from-placement` (`:203-205`) then says the whole content of the brief's
proposition is PLACEMENT: given only `⟨ fst G ∈ Lset β ⟩`, the truncated
existence follows, at every `a` and every `D`.

`code-exists` (`:227-229`) discharges the placement at the one site where the
statement lets it be discharged: `a := G`, so `β = stageBound G` contains
`stage G`, and `Lset-mono` lands the graph. `Site` is that choice, at `:224-225`.

**What this proves.** The proposition the brief names is true at `+ω ω`. **It is
also true at every other ordinal, and at every non-ordinal `D`, for the same
reason.** A statement that holds at every `D` measures nothing about `+ω ω`.

**WHAT IT DOES NOT PROVE, and I mark it.** I did not measure placement at the
INTENDED site `a := D`. There `β = stageBound (fst δ) (snd δ) .fst`, and
`stageBound` guarantees only `⟨ stage δ ∈ˢ β ⟩` (`src/L/Choice/Stage.lagda.md:366-368`,
through `bound2` at `src/L/Ordinal.lagda.md:185-188`). A graph with domain `δ`
holds pairs built over members of `δ`, so it is born above `stage δ`, and
nothing delivered puts it inside `Lset β`. **That residue is bookkeeping about
stages, not cardinal arithmetic**, and I did not build it because it does not
change the finding: the three conjuncts are free wherever the witness sits.

## 3. WHAT LEG 1 ACTUALLY IS

`[LJ-1.384]` stated leg 1 correctly and the brief did not.
`agents/tasks/LJ-1-384/lj-1.384-report.md:58-60` asks for「a `Good` that codes
an injection **of the square into δ**」. The brief hardened「a `Good` that
codes ...」into「the `Good` of `src/L/Cardinal.lagda.md:187-190`」, and that
`Good` codes neither the square nor the into.

`Leg1` at `Probe386.agda:287-291` states what the route needs, in full:

```agda
Leg1 P = ((⟪ fst δ ⟫ × ⟪ fst δ ⟫) ↪ ⟪ fst P ⟫)
       × ∥ Σ[ A ∈ Mem (Lset (SiteBound.β P)) ]
             InjCode (SiteBound.up P A) P δ ∥₁
```

and `leg1-gives-sq` at `:294-295` closes the route from it: `Leg1 P → sq (fst δ)`,
**untruncated**, with no axiom beyond the `lem` the whole tree already carries.

So the two unbuilt objects are named exactly:

- **The internal square `P`, with its ambient bridge.** An L-set whose index
  type receives `⟪ fst δ ⟫ × ⟪ fst δ ⟫`. **MEASURED: `src/` has no cartesian
  product of two L-sets.** `grep -rn "product\|Product" src/L/ src/V/ src/FOL/`
  returns 12 lines and every one is prose or the lexicographic ORDER at
  `src/L/Ordinal/SquareLaw.lagda.md:66`, which is an order on an ambient
  product type and not a set. The filter is literal; a differently spelled
  construction would escape it.
- **The coded injection with values in `δ`.** This is the cardinal arithmetic,
  and it is the only place cardinal arithmetic enters the route.

**Both are absent, and neither is what the brief asked me to measure.**

## 4. THE DOOR, MEASURED

`code-untruncates` (`Probe386.agda:264-268`) is the result that matters:

```agda
code-untruncates : (a b : S)
                 → ∥ Σ[ A ∈ Mem (Lset (SiteBound.β a)) ]
                       InjCode (SiteBound.up a A) a b ∥₁
                 → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
```

The hypothesis is TRUNCATED and the conclusion is DATA. Three delivered pieces
do the work and I added none: `orderAt` (`src/L/Choice/Step.lagda.md:730-731`)
gives the well-order of the stage; `leastOf`
(`src/L/WellOrder/Base.lagda.md:158-160`) selects the least code under `lem`,
which is the tree's own parameter and not a choice principle; `Small`
(`src/L/Coding/Injection.lagda.md:123-150`) reads the chosen code out.

**This generalises `agents/tasks/LJ-1-299/NoInj2.agda:107-110`**, whose
`readback` consumed the code as DATA. Here the code arrives truncated.
`NoInj2.agda` re-checked fresh this session, exit 0 (section 7), so the shape
the brief cited is green today.

**THE LIMIT, AND THE ARCHIVE NAMES IT.** The door returns an INJECTION. It
returns no bijection and no equivalence, so it moves neither wall the record
already carries: `archive/src/2026-08-09-rud-route/Everything.lagda.md:307-308`
closed the square law at the higher limits against a canonical BIJECTION, and
`archive/dev/JOURNAL-archived.md:1732` records the untruncated EQUIVALENCE as
still unavailable. Section 10 quotes both. **A reader who takes this door for
either wall's cure reads more than I measured.**

**Where each half is paid.** TWO untruncations happen in this term and
neither is a choice principle. The CODE is untruncated by `leastOf` on
`orderAt`, which needs a proposition-valued predicate; `isPropInjCode` at
`Probe386.agda:253-254` supplies that, and the spend is `lem`, the tree's own
parameter. The VALUE of the graph at a member is untruncated inside `Small`, by
`Extract.toVal` at `src/L/Coding/Injection.lagda.md:98-99`, whose `isPropFib`
(`:93-96`) rests on the `svAt` conjunct. **That second half is unique choice,
which `dev/literature/truncation-and-selection.md:92-95` records as the one free
case.** So the route adds no axiom.

## 5. PREMISES, EACH MARKED

1. 「`leastOf` turns the mere existence into DATA with no choice principle」
   (brief, basis `src/L/Cardinal.lagda.md:194-195`). **VERIFIED**, read at
   those lines, and SPENT: `code-untruncates` is that device at the four
   conjuncts instead of three.
2. 「`small-inj` reads a coded injection out to an ambient injective
   function」(basis `src/L/Coding/Injection.lagda.md:147-151`). **VERIFIED**,
   read at those lines, and spent in `code-untruncates` and `code-inj`.
3. 「`+ω` is the named band candidate and its union representation is sealed」
   (basis `src/L/Ordinal/StageArith.lagda.md:41-42`). **HALF VERIFIED.** The
   seal is at `:40-42` and it held: my probe names `+ω ω` in a type and
   nothing unfolded, which is P-l met. **The other half is NOT at that
   citation.** See section 6.
4. 「Two of the route's three legs are delivered and only leg 1 is missing」
   (basis `agents/tasks/LJ-1-384/lj-1.384-report.md:58-74`). **VERIFIED for
   legs 2 and 3**, and both are now spent inside one term. **CORRECTED for leg
   1**: leg 1 as the brief states it is free (section 2), and leg 1 as
   `[LJ-1.384]` states it needs two objects, not one (section 3).
5. 「`[LJ-1.375]` section 3.4 closed the door by saying an internal choice set
   would still need an external read-out」(basis
   `agents/tasks/LJ-1-375/lj-1.375-report.md:346-349`). **VERIFIED at those
   lines**, read myself: 「An internal choice set would still need an external
   read-out, which is the same untruncation.」 **REFUTED by measurement**, not
   by argument: `code-untruncates` is that read-out and it is not the same
   untruncation.

## 6. A CAUTION THE BRIEF DOES NOT CARRY

**Nothing in the tree certifies that `+ω ω` is a band ordinal. MEASURED.**

- `+ω` has ZERO consumers in `src/`: `grep -rln "+ω" src/` returns exactly
  `src/L/Ordinal/StageArith.lagda.md`. So `+ω ω` is a probe-level object only.
- `[LJ-1.332]` marked the two facts INFERRED and unbuilt:
  `agents/tasks/LJ-1-332/lj-1.332-report.md:125-128`, 「that `+ω ω` is a LIMIT
  and that it fails `Init`. **I built neither.**」
- **No dispatch has built either. MEASURED**: `grep -rn "Init (+ω" src/ agents/`
  returns 3 lines, and not one is a proof. Two are the marks themselves,
  `agents/tasks/LJ-1-332/lj-1.332-report.md:388` and
  `agents/tasks/LJ-1-334/lj-1.334-report.md:65`; the third is this report. The
  second of those prices the gap exactly: 「`ω · 2` injects into `ω × ω`, a
  counting fact this tree does not deliver」.

**So a measurement at `+ω ω` measures one site whose band membership is
itself inferred.** C-42 binds: a result here says nothing about how far the
shape extends, and it does not transfer to a general band ordinal by analogy
(P-l). `+ω u` is the supremum of the finite iterates above `u`
(`src/L/Ordinal/StageArith.lagda.md:34-42`), so `+ω ω` is `ω · 2`, which is how
`[LJ-1.334]:65` spells it. That row also records the counting fact the tree does
not deliver. **So an ambient pairing at this one ordinal, if anyone built it,
would rest on counting and would say nothing about the band, whose difficulty is
uniformity over unnamed limits. I built no pairing at `+ω ω` and I claim none.**

## 7. RUNS, FLOOR, SLOTS (C-53, C-12)

Empty-file floor: `Floor386.agda`, exit 0, **0.07 s**. Every figure is WARM:
the `src/` interface chain was already built. **P-l forbids pricing any landing
from these**, and I price no landing.

| run | file | exit | real s |
|---|---|---:|---:|
| 1 | `LJ-1-386/Floor386.agda`, the floor | 0 | 0.07 |
| 2 | `LJ-1-386/Probe386.agda`, first full check, **GREEN** | **0** | 4.35 |
| 3 | `LJ-1-386/Probe386.agda`, after the PART 5 refactor | 0 | 4.21 |
| 4 | `LJ-1-386/Probe386.agda`, re-check, own interface warm | 0 | 1.37 |
| 5 | `LJ-1-299/NoInj2.agda`, premise 2's shape, re-checked FRESH | **0** | 2.57 |
| 6 | `LJ-1-386/Probe386.agda`, re-checked AT THE AMENDMENT | **0** | 2.36 |

Slots: `pgrep -fl agda` returned no other agda process before every
invocation; one process was mine. `GHCRTS` was set on the pane by the program
and I never set it. No heap exhaustion, so no WALL event.

Machine: 1-minute load 2.85 when the timing batch that produced rows 1, 4 and 5
started, and 2.85 again at row 6. I report no seconds as a price, so the load
damages no figure. Row 6 confirms the amendment moved no Agda: I edited only
this report, and `pgrep -fl agda` before it returned the watchdog shell and no
Agda process.

## 8. W3: THE WIDEST UNMEASURED TERM, AND ITS PROBE

**The widest unmeasured term is no longer「leg 1」.** It is the internal square
`P` with its ambient bridge (section 3, first bullet). **I give no line figure,
because no basis exists.** `[LJ-1.327]`'s ABOUT 820 priced coding
`pairomega`'s well-founded recursion, a different object, and P-l forbids the
transfer. The nearest delivered comparable is the range set built by
replacement inside `src/L/Coding/Injection.lagda.md:186-218`, which is 33
lines and builds a set from ONE formula with functionality; a cartesian product
needs two nested replacements and a pair-membership reading, so it is a
comparable of shape and not of size. **The next probe should build `P` and its
bridge alone**, with `Leg1` at `Probe386.agda:287-291` as its exact obligation,
because `leg1-gives-sq` already closes everything after it.

The probe is tracked, it is in `agents/tasks/LJ-1-386/`, it is never deleted,
and I ran it while this task was live.

## 9. W2 AND DD4: WRITE IT GENERIC

This probe lands nothing, so it moves no shared line. The judgement the clause
asks for:

- **`code-untruncates` is stated at ARBITRARY `a` and `b`, not at the band.**
  Its two parameters are plain L-elements. So the door, if it is ever landed
  in `src/`, serves the AC wing and the GCH wing without a fork, and it
  consumes only chapters both wings already consume (`L.Choice.Step`,
  `L.WellOrder.Base`, `L.Coding.Injection`).
- **The internal square is the piece at risk of being written fixed.** A
  product of two L-sets is generic by nature; a square of one ordinal is not.
  **Write the product, not the square.** A stop-line is never a reason to write
  the fixed form, and this report contains no line figure that could be read as
  one.

## 10. ARCHIVE USED

**WHEN THIS SURVEY RAN, AND I STATE THE ORDER PLAINLY.** I ran it at the return,
after the probe was green, and not before I wrote the Agda. Clause W8 asks for
the injected block BEFORE the Agda, and I did not keep that order. **The survey
overturned no finding. It added one LIMIT**, which the first two bullets hold and
section 4 now carries.

- `archive/src/2026-08-09-rud-route/Everything.lagda.md:307-308`. **BEARS, and it
  is the nearest recorded statement of my own obstruction.** The retired route's
  catalog says of its square law that "the least-of search returns its witness
  only up to truncation, and no canonical bijection exists to make it honest".
  **THE NOUN IS BIJECTION.** `code-untruncates` returns an injection, so it does
  not reopen what that chapter closed. Section 4 measures a different door, and
  this line is the reason the two do not collide.
- `archive/dev/JOURNAL-archived.md:1732`. **BEARS, as the same limit in the
  campaign's own words.** The `[T47]` entry ends "The untruncated equivalence
  remains unavailable (T31's wall)". An equivalence is not an injection either.
  **So T31's wall stands after my measurement.**
- `archive/dev/TASKS-archived.md:82`. **BEARS, as the measured history of the
  object leg 1 needs.** Row `L3.32-T47` reads "Truncated square law at initial
  ordinals" and its verdict is DELIVERED. Two neighbours price the rest:
  `archive/dev/TASKS-archived.md:66` reads "Square law, discharged" with verdict
  "DELIVERED (transfer blocked)", and `archive/dev/TASKS-archived.md:78` reads
  "Where counting calls the square law" with verdict "RED (wall confirmed)".
  **The retired route therefore delivered a TRUNCATED law and no untruncated
  one**, and the counting call site was the red. That is the shape section 3
  found again at the band, on the live route.
- `dev/ARCHIVE.md:267`. **BEARS as a shape precedent and never as a route.** The
  retired module `L.Rud.CodeSet` is recorded with "membership definitional,
  decode untruncated, every code unconditionally a closure member". An
  untruncated decode of a code family is section 4's shape. **The precedent does
  not transfer.** That family is the rud route's, the row reads "Retired
  2026-08-06 under D17 and D20", and the live tree codes through `L.Coding`.
  P-l forbids carrying its figures across.
- `archive/dev/DECISIONS-archived.md:44`. **BEARS as this task's own funding
  rule.** Archived D22, "Every block is gated before it is funded", says "the
  probe is therefore not caution but arithmetic". **It states the same rule as
  D-1 in this brief's LAWS block, and it gives the arithmetic reason D-1's
  one-line form drops.** That is why a NO-GO here would have been a full return.
  I read the heading and the opening of every other row of the archived D
  series, and none of them bears on a coded witness.

## 11. LITERATURE USED

Clause W8 binds this section. **The literature returns no NO-GO.** It states the
exact condition section 4's device meets, and it names what that device can never
give.

- `dev/literature/truncation-and-selection.md:146-148`. **BEARS, and it is the
  decisive entry.** It states the constraint on `leastOf`: it "delivers the least
  INDEX untruncated, and any payload it delivers with the index is a
  proposition". **`code-untruncates` sits inside that condition.** Its index is
  the code, which comes out as data, and its payload is `InjCode`, which
  `isPropInjCode` at `Probe386.agda:253-254` proves is a proposition. So the door
  needs no new axiom. **The same line bounds the door**: a data payload beside
  the index does not come out, which is why the route reads the function back
  through `Small` and not out of `leastOf`.
- `dev/literature/truncation-and-selection.md:92-95`. **BEARS, as the free case
  section 4 already spends.** It reads "This is the only free case." My section 4
  names both spends and neither is outside it.
- `dev/literature/devlin-II5.md:413-418`. **BEARS, as the classical price of the
  leg I did not build.** It records the level-size equation and says "It is
  generic cardinal arithmetic over the level-size equation". **That is the
  counting content section 3 leaves unbuilt**, and it sits on the Def tower,
  which is this campaign's trophy tower.
- `dev/literature/digest.md:240-241`. **BEARS as a comparable of SHAPE.** It
  records the "surjection g : α -> J_α^A when α is closed under Gödel pairing" at
  SZ 1.17. Closure of a level under a pairing is the classical shape of leg 1.
  **It is the J tower's, so it prices nothing here** and P-l forbids the
  transfer.
- `dev/literature/terms-2026-08.md:290-293`. **BEARS, and it corroborates section
  6 from a source I did not write.** The dossier records the square law as "the
  classical square law for infinite ordinals", and records it "cited as a bound,
  not proved as a theorem" in this tree. **So the counting fact the band needs is
  NAMED in the live tree and is not PROVED there.** Section 6 reached that by its
  own greps; this is a second, independent measurement of it.
- `dev/literature/geology.md:3-4`. **DECLINED, and nothing in it bears.** Its
  purpose line reads "fetch and pin the set-theoretic geology primary sources
  that the in-repo corpus currently lacks". It serves the geology phase, `[L6]`.
  A grep of the whole file for pairing, square, truncation and band returns 0
  hits.

## WHAT I DID NOT DO

I built no internal square and no internal pairing, and I refuted neither
(C-36 binds both directions). I built no proof that `+ω ω` is a band ordinal
and I claim none. I did not touch `src/`, any sibling's files, or any EXPECTED
RED probe. I ran no `make` target, no `make check`, no commit, no push, no
checkout, no stash, no reset, no clean. I did not edit `dev/PLAN.md` or any
record outside my task directory.

## GATES RUN ON MY FILES

- `.venv/bin/python scripts/gate/lint-agda.py --check` on `Probe386.agda` and
  `Floor386.agda`: exit 0.
- `.venv/bin/python scripts/gate/check-probes.py --check`: clean, 3478 tracked
  files, no probe outside `agents/tasks/`.
- No em dash in any file I wrote: a grep for U+2014 over both Agda files and
  this report returns 0 hits. The pattern is named by codepoint here, because
  writing it out would put the character in the file it certifies.

**RE-RUN AT THE AMENDMENT.** Acceptance conjunct 6 is a pinned member list
(`scripts/pod/accept.py:86-93`) plus one per-task checker
(`scripts/pod/accept.py:212-224`), so I ran all seven. `lint-agda`,
`lint-prose`, `check-glossary`, `check-fences`, `check-probes` and
`weave-i18n --check` each exit 0. `check-survey-quotes.py LJ-1.386` now exits 0
and prints "clean (0 note(s), 0 defect(s))". **That last checker is the one that
refused this return, and sections 10 and 11 are its cure.**

**CONJUNCT 5 WAS NOT MINE, AND I MEASURED THAT RATHER THAN ASSUMED IT.**
`agents/tasks/LJ-1-386/runs/accept-1.out` records conjunct 5 FAILED and gives
the record's error class as `spec_surface`. The checker is green today and the
cause sits outside my scope. THREE ITEMS, each checkable:

- `.venv/bin/python scripts/pod/check-spec-surface.py --check` exits 0 and
  prints "clean (8 surface file(s), 201 declaration(s), 8 guarded rule home(s),
  499 in-fence lines)".
- `git diff dev/pod/spec-surface.toml` moves 6 lines and NOT ONE of them is a
  `[[declaration]]`. It moves `generated` from 2026-08-18 to 2026-08-19, and the
  hashes of five `[[guarded]]` rule homes: `AGENTS.md`,
  `dev/memos/LJ-4-pod-program-design.md`, `dev/pod/heads.toml`,
  `dev/pod/instructions/maintainer.md` and
  `dev/pod/instructions/mathematician.md`. **So the red was R16's rule-home
  half and never R9's trophy half.**
- The snapshot's mtime is 2026-08-19 12:51:11. `accept-1.out` reads
  "# started 2026-08-19 12:18:49". **The regeneration lands after the acceptance
  run that failed on it**, so the acceptance measured a tree whose guarded homes
  had moved and whose snapshot had not.

**My write scope is `agents/tasks/LJ-1-386/`, and the record agrees.** Its
`changed_files` are my four files and nothing else, and no guarded rule home is
among them. I did not edit the snapshot and I never ran the checker's `--write`
mode.

## 12. CODER RE-MEASUREMENT, 2026-08-20

slot: `coder`. Written incrementally (C-22). No commit, no push. I wrote
only in `agents/tasks/LJ-1-386/`. The program set `GHCRTS="-A64m -I0 -M8g"`
on this pane. I never set it. One Agda process. No heap event.

This dispatch received the same brief with `head_slot: coder`. The probe
and the report above were already in the tree from the 2026-08-19
mathematician run (`dev/pod/transitions/2026-08.jsonl:12-26`). I did not
rewrite `Probe386.agda`. Later tasks cite it at `file:line`
(`dev/pod/queue.toml:73`, `agents/tasks/LJ-1-388/lj-1.388-report.md:49`,
`agents/tasks/LJ-1-397/Probe397.agda:20`). The 2026-08-20 audit marked
386 CLEAN (`dev/pod/audit-2026-08-20.md:161`). I independently read the
named types, then I ran the file.

### 12.1 Types I read myself

- `Good` at `src/L/Cardinal.lagda.md:187-190` is three conjuncts. It names
  no target. The fourth `InjCode` conjunct is at `:228`.
- `leastOf` at `src/L/WellOrder/Base.lagda.md:158-160` takes truncated
  existence and returns data. Premise 1 holds at those lines.
- `small-inj` at `src/L/Coding/Injection.lagda.md:147-150` reads a coded
  injection to an ambient injection. Premise 2 holds at those lines.
- `+ω` is opaque at `src/L/Ordinal/StageArith.lagda.md:40-42`. Premise 3's
  seal holds at those lines.
- `hasReplacementL` at `src/L/Axioms/Full.lagda.md:277-280` is the
  replacement the identity graph spends.
- `code-exists` at `Probe386.agda:227-229` is the brief's proposition at
  `D := +ω ω`, with the search site equal to the graph. `code-inj` at
  `:238-242` is the identity on `⟪ fst δ ⟫`.

**`phi-less` is not in `src/`.** MEASURED this dispatch:
`grep -n phi-less src/` returns 0 hits. The brief asked me to try
`orderAt`, `phi-less` and replacement. Replacement is what the probe
spends. `orderAt` is spent inside `code-untruncates`
(`Probe386.agda:276`). `phi-less` is a name in the brief and in
`agents/tasks/LJ-1-384/lj-1.384-report.md:104`. It is not a delivered
identifier. That does not block the named obligations.

### 12.2 W2

`code-untruncates` (`Probe386.agda:264-268`) is at generic `a` and `b`.
The identity graph (`Probe386.agda:94`) is at generic `D`. Nothing in the
probe is written fixed at `+ω ω` except the two named obligations. No
deadline forced a fixed form.

### 12.3 Predecessor types (audit F1/F3 clause)

- `[LJ-1.384]` verdict is ESCAPE-OPEN, not NO-GO
  (`agents/tasks/LJ-1-384/lj-1.384-report.md:17`). I did not inhabit a
  refuted type.
- `[LJ-1.299]` `readback` at `agents/tasks/LJ-1-299/NoInj2.agda:107-110`
  is the delivered shape `code-untruncates` generalises. That probe is
  green in the tree. I did not change it.

### 12.4 Runs (this dispatch)

Empty-file floor, then the probe. Both WARM: `_build/2.8.0/agda/src/L/Cardinal.agdai`
was already present. P-l forbids pricing a landing from these numbers. I
price no landing.

| run | file | exit | real s |
|---|---|---:|---:|
| 7 | `LJ-1-386/Floor386.agda`, the floor | **0** | 0.05 |
| 8 | `LJ-1-386/Probe386.agda`, this dispatch | **0** | 1.55 |

Slots: `pgrep -fl agda` before each invocation returned only
`scripts/ops/agda-watchdog.sh`. One process was mine. `GHCRTS` was
`-A64m -I0 -M8g` on the pane. I never set it. No heap exhaustion, so no
WALL event.

Machine: 1-minute load 3.46 at the floor and 3.26 at the probe. I report
no seconds as a price.

**GATES ON THIS ADDENDUM.** `lint-agda.py --check` on `Probe386.agda` and
`Floor386.agda`: exit 0. `check-probes.py --check`: clean, 3703 tracked
files. `check-survey-quotes.py LJ-1.386`: clean (0 note(s), 0 defect(s)).
No em dash in any file in this directory.

### 12.5 Coder verdict

**GO on the two named obligations.** `code-exists` and `code-inj` typecheck
at `agda --safe`, exit 0. The brief's proposition is inhabited at `+ω ω`
by the identity graph. That inhabitant carries no cardinal arithmetic, so
it is not a pairing of the square into the band. Sections 2 to 4 of this
report already name that limit. I measured the same facts at the same
`file:line` values, and I did not reopen them.

What the next brief still needs is unchanged: the internal product `P`
with its ambient bridge, and a coded injection from `P` into `δ`, which
is `Leg1` at `Probe386.agda:287-291`. `[LJ-1.388]` later built the first
conjunct. I did not rebuild it here.

I built no pairing and no placement at `a := δ`. I did not touch `src/`.
I ran no `make` target, no commit, no push.
