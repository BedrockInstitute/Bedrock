# LJ-1.368 report: DD25 adversarial review of `[LJ-1.365]`'s SET-MOTIVE refutation

tier: opus (pi-subagent-mode), the ADVERSARIAL row, in-harness. It lands nothing.
Written incrementally (C-22). No commit, no push. **I wrote no file outside
`agents/tasks/LJ-1-368/`.** `git status` also lists changes under `src/`,
`dev/` and `scripts/`. **They are NOT mine**: they were present when I started
and they belong to other sessions. I ran `agda` on `src/` files, and a
typecheck writes only into `_build/`.

## VERDICT

**SPLIT.**

**The outcome survives and the stated mechanism does not.** Something beyond one
`PT.rec` is still necessary, so `[LJ-1.301]`'s aside is not vindicated. But the
necessary thing is NOT what `[LJ-1.365]` names. `[LJ-1.365]` says the chain
crosses a SET goal between the trophy's conclusion and the band, and that the
crossing blocks the wrap. **That inference is MEASURED FALSE.** One `PT.rec`
carries the whole delivered chain THROUGH that same set-typed injection into
the trophy's own conclusion type, exit 0. The residue is one different
statement, and it is smaller than the untruncation.

**Three of `[LJ-1.365]`'s sentences fail.**

1. 「the chain crosses data goals, and the first one is a SET」
   (`agents/tasks/LJ-1-365/lj-1.365-report.md:12-13`) as a reason the wrap
   fails. REFUTED by `one-rec-through-injection`,
   `agents/tasks/LJ-1-368/Probe368.agda:154-161`, exit 0.
2. 「no delivered use site consumes the law under a propositional motive」
   (`lj-1.365-report.md:13-14`). FALSE. The delivered use site's own conclusion is `⟨ x ∈ˢ Lset κ ⟩`,
   `src/L/BoundedSubset.lagda.md:1621-1622`, an hProp. `[LJ-1.333]` had already
   measured this and had written the warning:「A future brief must not repeat
   the search for a propositional motive: it is already there」,
   `agents/tasks/LJ-1-333/lj-1.333-report.md:331-332`.
3. 「The body cannot exist」 (`lj-1.365-report.md:10`). NOT MEASURED. An exit 42 on `PT.rec squash₁ ...`
   is the C-45 mirror the brief named. C-54's own text says the opposite of
   this sentence: a stall at a set motive is 「a term you have not written
   rather than an axiom the theory lacks」, `dev/LESSONS.md:4405-4406`.

**And `[LJ-1.365]`'s central control measures less than it reports.** SoloC2's
exit 42 shows that `squash₁` does not prove `isProp` for a type that is not
literally a truncation. It does not read the goal's h-level. Section 2 gives
both halves of that control, green and red, in one session.

**What re-opens.** The debt moves from an untruncation of `sq` to ONE
truncated-conclusion choice statement over the band's Pi. The untruncation
implies it (MEASURED). The converse is not available here (INFERRED). The
literature digest says the standard axiom of choice delivers exactly this
shape and no more, `dev/literature/truncation-and-selection.md:229`. So the
cheapest cure on the GCH path is not closed. It is one named statement away,
and the statement is weaker than the one `[LJ-1.332]` left open.

## 1. WHAT I RE-RAN, AND THE THREE MEASUREMENTS

Every run: ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. Slots
counted before every invocation with the brief's exact command. The count read
0 or 1 before every run, and the cap is TWO, so I never waited. No heap
exhaustion. Empty-file floor, `Floor368.agda`, same pass as the table: **0.81 s**.

| run | file | exit | real s |
|---|---|---:|---:|
| floor | `LJ-1-368/Floor368.agda` | 0 | 0.81 |
| target, re-run | `LJ-1-365/ProbeLJ1365A.agda` | **0** | 2.46 |
| target, re-run | `LJ-1-365/SoloC2.agda` | **42** | 1.49 |
| mine, GREEN | `LJ-1-368/Probe368.agda` | **0** | 1.77 |
| mine, control A | `LJ-1-368/MustFail368A.agda` | **42** | 1.18 |
| mine, control B | `LJ-1-368/MustFail368B.agda` | **42** | 1.57 |
| mine, control C | `LJ-1-368/MustFail368C.agda` | **42** | 1.48 |

All figures are warm on `src/` and on the sibling probes' interfaces. They
price the marginal check and not a cold build (P-l).

**The brief's three measurements, with my own exit codes.**

1. **THE TOP WRAP TYPES. CONFIRMED.** `ProbeLJ1365A.agda` re-runs exit 0. It
   carries `wrap-top` at `:116-121` and `inj-set` at `:160-163`, so both the
   first and the third measurement re-run green in one process.
2. **THE PINNING IS REAL. CONFIRMED, and it needed a control.** The brief asked
   whether `statement-fits` pins the spelling. I built the missing control.
   `MustFail368C.agda:52` offers the delivered `GCHStatement` a conclusion that
   differs in ONE conjunct: `InjL (𝒫 κ) δ` becomes a second `InjL δ (𝒫 κ)`.
   Agda refuses, exit 42, and prints both types side by side. So the hand
   spelling IS machine-checked, and `[LJ-1.365]` part 1 stands.
3. **SoloC2 IS RED, AND IT MEASURES LESS THAN THE REPORT SAYS.** Exit 42
   re-runs. My message differs from the report's in the metavariable name only
   (`∥ _A_19 ∥₁` here, `∥ _A_21 ∥₁` in the report). Section 2 is the finding.

**One small correction.** `[LJ-1.365]` writes 「The file is 69 lines long」 about
`src/L/GCH.lagda.md`. It is 70 lines, MEASURED by `wc -l`. The conclusion's own
range, `:65-68`, is right, and the stale `:85-87` correction against
`[LJ-1.301]` is right.

## 2. WHAT `squash₁`'s REFUSAL MEASURES

**The control the target did not run, in two halves, one session.**

`squash₁ : (x y : ∥ A ∥₁) → x ≡ y`. So `PT.rec squash₁` demands that the MOTIVE
unify with `∥ _ ∥₁`. A motive that is a proposition, and is not literally a
truncation, is refused too.

- **GREEN half.** `path-motive-ok`, `Probe368.agda:122-124`, exit 0. Motive
  `x ≡ y` for `x y : ⟪ δ ⟫`. That motive IS a proposition, because `⟪ δ ⟫` is a
  set. The eliminator's proof argument is the real `isProp`.
- **RED half.** `squash-at-a-path`, `MustFail368A.agda:37-39`, exit 42. The
  SAME term, the SAME motive, `squash₁` in place of the real `isProp`:

```text
(x ≡ y) !=< ∥ _A_21 ∥₁
when checking that the expression squash₁ has type isProp (x ≡ y)
```

**That is SoloC2's message shape at a motive this session proved propositional.**
So an exit 42 of this form cannot support 「the goal is not a proposition」.
MEASURED.

**The same point from the other side, and I found it by accident.**
`squash-serves-∈ˢ`, `Probe368.agda:126-128`, exit 0: `squash₁` SERVES the motive
`⟨ δ ∈ˢ ω ⟩`, because that hProp unfolds to a truncation. **So `squash₁`
succeeds exactly when the motive unfolds to `∥ _ ∥₁`, and it fails exactly when
the motive does not. Neither outcome reads the h-level.**

`inj-set` is green and it is not the missing half. `isSet` does not refute
`isProp`, because every proposition is a set. Nothing in `[LJ-1.365]` measures
that `⟪ Lset α ⟫ ↪ ⟪ α ⟫` fails to be a proposition. **INFERRED, not measured,
and I did not measure it either:** the type has many inhabitants at `α = ω`, so
the h-level claim is very probably true. It is also not load-bearing, because
section 3 shows no assembly must eliminate there.

## 3. DOES EVERY PATH CROSS A SET, OR ONLY THE PROBE'S?

**ONLY THE PROBE'S. MEASURED.**

**The green counter-route.** `one-rec-through-injection`,
`Probe368.agda:154-161`, exit 0:

```agda
one-rec-through-injection :
    (zf : ModelL.isZFModel) (κ : hPropStructure.S 𝒮ʟ)
  → (oκ : IsOrd (fst κ)) (cκ : IsCardinalL κ)
  → (κ∉ω : ⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → (use : StageCards → Concl zf κ oκ cκ κ∉ω)
  → ∥ LimitBand ∥₁ → Concl zf κ oκ cκ κ∉ω
one-rec-through-injection zf κ oκ cκ κ∉ω use =
  PT.rec squash₁ (λ lb → use (cards-from-band lb))
```

`StageCards` is the delivered `⟪ Lset α ⟫ ↪ ⟪ α ⟫` at every infinite stage,
`Probe368.agda:147-149`, and `cards-from-band` is `[LJ-1.337]` probe D's own
`stage-card-from-band`, `agents/tasks/LJ-1-337/ProbeLJ1337D.agda:41-46`. **So
this term crosses exactly the set that SoloC2 is refused at, and it crosses it
inside the body of ONE `PT.rec`.** A set-typed term built UNDER the wrap is
never an elimination site. **A data goal in the chain does not block the wrap by
itself, MEASURED.**

**Where the elimination site really is.** The truncation enters the delivered
chain at the band, and it enters INSIDE a Pi: `limit-truncated` returns
`∥ sq δ ∥₁` per δ (`agents/tasks/LJ-1-332/ProbeLJ1332A.agda:196-204`), while
`L.StageCardinal` consumes `sq δ` per δ (`src/L/StageCardinal.lagda.md:17-19`)
and `Devlin55.BoundedSubsetAt` takes the same family
(`src/L/BoundedSubset.lagda.md:1388-1390`). Push the truncation out of that Pi
and Agda names the goal itself. `MustFail368B.agda:42-45`, exit 42:

```text
when checking that the expression squash₁ has type isProp (sq δ)
```

**The first data goal any assembly meets is `sq δ`, not the injection.**
`[LJ-1.365]` printed the injection instead, and reached it only by choosing to
wrap there.

**What every path DOES cross, and I mark the strength.** MEASURED: at least one
path to the conclusion crosses no set MOTIVE. INFERRED, and C-36 binds: every
path must pass the band's Pi of truncations, because that Pi is where `sq`
enters the delivered chain at non-initial limits, and `[LJ-1.332]` delivers no
other supplier there.

**The residue, stated exactly.** `BandChoice`, `Probe368.agda:226-227`:

```agda
BandChoice = LimitBandT → ∥ LimitBand ∥₁
```

`closes-from-choice`, `Probe368.agda:229-236`, exit 0: `BandChoice` plus one
`PT.rec` gives the trophy's conclusion, with NO untruncation of `sq` anywhere.
`choice-from-untruncation`, `Probe368.agda:241-242`, exit 0: the untruncation
`[LJ-1.332]` asks for implies `BandChoice` in one line. **So `BandChoice` is no
STRONGER than the open debt, MEASURED. That it is strictly WEAKER is INFERRED,
and my basis is the literature and not a term:** HoTT Book 3.8.1 and Lemma 3.8.2
give AC a truncated conclusion of exactly this shape
(`dev/literature/truncation-and-selection.md:225-229`), while a general
untruncation is the taboo-adjacent object the same digest says must be ruled on
(`:216-221`).

**This is C-56 in its exact form.** The wall was in the ASSEMBLY. The
mathematics did not move.

## 4. WHICH ELIMINATORS WERE TRIED, AND WHICH WERE NOT

**Tried by `[LJ-1.365]`:** `PT.rec` with `squash₁`, at three goals (ProbeLJ1365A
part 2, ProbeLJ1365C control 1, SoloC2, SoloC3); and `PT.SetElim.rec→Set`,
STATED green at the injection goal (`ProbeLJ1365A.agda:175-178`).

**So the brief's suspicion is half right.** The target did not try only
`PT.rec`. It did state C-54's set eliminator. **But it applied C-54 at a goal no
assembly needs, and `[LJ-1.333]` had already stated the same door at the goal
that matters:** `item2-door` at `sq α`,
`agents/tasks/LJ-1-333/lj-1.333-report.md:158-164`. `c54-at-injection` is that
delivered term relocated to the probe's own chosen site.

**The library inventory, MEASURED at
`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/Cubical/HITs/PropositionalTruncation/Properties.agda`.**

| eliminator | line | motive it needs | does it serve a data goal |
|---|---:|---|---|
| `rec` | 33 | proposition | no |
| `rec2`, `rec3` | 37, 42 | proposition | no |
| `elim`, `elim2`, `elim3`, `elim'` | 91, 98, 106, 165 | proposition | no |
| `map`, `map2` | 170, 173 | truncation | no |
| `rec→Set` | 185 | set, plus `2-Constant` | **yes, at a price** |
| `elim→Set`, `elim2→Set` | 270, 291 | set family, plus coherence | **yes, at a price** |
| `rec2→Set` | 567 | set, two truncations | **yes, at a price** |
| `recFin`, `recFin2`, `elimFin` | 56, 72, 114 | proposition, FINITE index | **family, finite only** |

**Two readings matter.**

- Every propositional-motive eliminator is useless at a data goal, so naming
  `rec2` or `elim` adds nothing. The brief's attack 3 is answered NO on the
  substance: no untried eliminator rescues a data goal.
- **`recFin` is the informative row.** It is the library's OWN answer to the
  Pi-of-truncations question, and it works for a FINITE index only. The band's
  index is an ordinal. **So the library itself says the family step needs
  something the eliminators do not contain, and that something is choice.**

**C-54 at the right goal, stated and green.** `band-from-endomap`,
`Probe368.agda:205-208`, exit 0: a weakly constant endomap of `sq δ`, per δ,
turns the pointwise band into the delivered band. **I built no such endomap and
I assume none** (C-36). This is `[LJ-1.333]` section 3.2's object, and its
measurement stands: the tree's only canonicalizer consumes the row the band
negates.

## 5. IS `stage-card-upper` THE ONLY SUPPLIER?

**YES for the ambient stage injection, MEASURED by grep over `src/`.** One
definition, `src/L/StageCardinal.lagda.md:564-566`. One re-export,
`src/L/BoundedSubset.lagda.md:1400-1402`. One consumer,
`src/L/BoundedSubset.lagda.md:1513`. `[LJ-1.365]`'s citation is correct.

**But the brief's real question is the second half, and the answer changes the
verdict.** The brief asks whether a coded supplier exists that never leaves the
truncation. **A new supplier is not needed, because the existing one already
sits under a propositional roof.** `Devlin55.BoundedSubsetAt` takes the whole
`sq` family as a module parameter, `src/L/BoundedSubset.lagda.md:1388-1390`, and
its only export is `theorem : ⟨ x ∈ˢ Lset κ ⟩`, `:1621-1622`. That type is an
hProp, and the delivered file itself eliminates a truncation at that motive at
`:1607`, with `PT.rec (snd (x ∈ˢ Lset κ))`.

`delivered-motive-is-prop`, `Probe368.agda:172-175`, exit 0, states the
consequence at the delivered types: ONE `PT.rec` over the WHOLE `SqBelow α`
family serves that conclusion.

**MEASURED:** the delivered consumer's conclusion type is an hProp, and one
`PT.rec` at it accepts the whole family. **INFERRED, and I say so plainly:** I
did not instantiate `Devlin55.BoundedSubsetAt` itself, so I did not run the
delivered proof under the wrap. I priced the shape, not the module.

## 6. WHAT `[LJ-1.332]`'s UNTRUNCATION IS WORTH AFTER THIS VERDICT

**It is worth strictly less than `[LJ-1.365]` leaves it worth, and the
difference is the whole value of this review.**

- **Before this review**, the record read: the untruncation is the sole blocker,
  five attempts failed, and a `PT.rec` at the use site cannot help.
- **After it**, the record should read: the untruncation is ONE of two doors.
  The other door is `BandChoice`, it is implied by the untruncation, and it
  closes the trophy's conclusion with one `PT.rec` and no canonicalizer.

**`[LJ-1.365]`'s sentence 「the wrap changes the debt's ADDRESS and not its
PRICE」, `lj-1.365-report.md:145`, is the sentence I would strike.** The wrap changes the price by one
measured implication.

**And one recorded objection to the choice door no longer applies here.** The
retired route rejected choice because 「a choice principle implies excluded
middle and would cost the tree's postulate-free claim」,
`archive/dev/JOURNAL-archived.md:1630`. **The live tree already spends LEM as a
module parameter of every chapter on this path** (`src/L/GCH.lagda.md:10`,
`src/L/StageCardinal.lagda.md:15`). So the Diaconescu objection has no force in
this tree. **I do NOT claim choice is therefore free.** AC is strictly stronger
than LEM, and it stays an ambient assumption the owner must rule on. I claim
only that the archived REASON for refusing it is spent.

**What I did not settle.** Whether `BandChoice` is derivable. Whether it is
strictly weaker than the untruncation. Whether a weakly constant endomap of
`sq δ` exists. C-36 binds all three, and I refuted none of them.

## 7. WHAT `[LJ-1.365]` GOT RIGHT

A review that only lists faults is not a measurement.

- `wrap-top` types at the real conclusion, and the conclusion is machine-pinned.
  Re-run exit 0. My control C proves the pinning is not vacuous.
- `inj-set` is green and correct.
- The stale-citation correction is right: `:65-68`, against `[LJ-1.301]`'s
  `:85-87`.
- Its section 2 point 2 names the family, and that IS the true shape. **The
  report knew the family mattered. It then priced the SET goal instead.**
- Its three doors in section 3 are the right three doors. The error is the
  claim that none of them moved.

## 8. DD4

**Axis named** (C-46, fixed at `scripts/measure/ledger.py:50`): the AC closure
against the GCH closure. No GCH endpoint exists in `src/` yet, so this sits on
the proxy axis, as every DD4 figure to date does.

**The verdict has a DD4 direction, and it points the other way from
`[LJ-1.365]`'s.** My route adds ONE eliminator outside the delivered chain. It
edits no consumer. `[LJ-1.337]`'s empty consumer diff survives untouched, and
the `sq` chain stays class-free. **The route
`[LJ-1.365]` steers toward is a SUPPLIER change inside `L.Ordinal.SquareLaw`**
(its ARCHIVE section recommends it, from the retired route's shape). **That is
shared code at the heart of both proofs. The wrap route is not.** So the
target's assembly gives up the strongest DD4 shape this chain has produced, and
it gives it up on an inference that does not hold.

## 9. ARCHIVE USED (DD18)

The four corpora, each named in one line, with a real quote per file read.

- **`archive/src/2026-08-09-rud-route/`**: READ and it BEARS, at two files, and
  it answers attack 3 directly. `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:502`:
  「`PT.rec (snd (x ∈ˢ α)) viaUnion`」. **The retired route's square law
  eliminated truncations at PROPOSITIONAL motives throughout, and it never used
  a set-motive eliminator: `grep` for `rec→Set`, `elim→Set` and `2-Constant`
  over the whole retired tree returns NOTHING, MEASURED.** The one richer
  eliminator it used is `rec2` at a path in a set:
  `archive/src/2026-08-09-rud-route/L/Rud/Images.lagda.md:192`:
  「`PT.rec2 (setIsSet w v) go H₁ H₂`」.
- **`archive/dev/JOURNAL-archived.md`**: READ and it BEARS HARD. It contains
  this exact finding, from the retired route, in three lines. `:1626`:
  「every consumer goal in the chain is a proposition」. `:1719`:
  「T43's recorded claim VERIFIES TRUE: the Core's induction hypothesis is
  eliminated in exactly one」 place, at a propositional target. `:1724`:
  「to CONSUME the truncated hypothesis one must still PROVIDE it at every」
  member. **So the retired route measured that consumption at a propositional
  goal is FREE, and that the cost is in the PROVISION over a family. That is my
  section 3, one route earlier.** `[LJ-1.365]` quoted this file at `:1697` and
  took the opposite reading from the same episode.
- **`archive/dev/DECISIONS-archived.md`**: NOT read. WHY NOT: `grep -c
  "truncat"` returns 0, so no truncation-policy ruling exists there, MEASURED by
  the empty grep.
- **`archive/dev/TASKS-archived.md`**: READ and it BEARS, as SHAPE. `:78`:
  「Where counting calls the square law」, RED, wall confirmed. The retired
  route walled at the counting site too, and the JOURNAL entries above record
  how it got past the wall.

## 10. LITERATURE USED (DD18)

`dev/literature/truncation-and-selection.md`, READ and it BEARS.

**In one line, as the brief asks: it names `elim→Set` at `:191`, which the
target did not name, and NO eliminator in it rescues a data goal without a
`2-Constant` map.** 「(`Properties.agda:270-274`) does the same for a dependent
set-valued motive.」

**The decisive paragraph is section 2.7, and it cuts FOR the wrap route.**
`:229`: 「So AC delivers `∥ f ∥₁` for a selection function `f`, never `f`.」 The
digest adds that AC does not help when the consuming goal is not a proposition.
**Here the consuming goal IS a proposition, at the trophy and at the delivered
theorem. So the case the digest warns about is not this case, and the standard
choice statement is exactly the shape `BandChoice` needs.**

`:16`: 「No classical source at this step uses choice.」 So the canonicalizer
route stays the honest cure, and `[LJ-1.333]` measured its exact blocker. The
two doors are both open.

## 11. WHAT I DID NOT DO

- I did not build `BandChoice`, and I refuted no map (C-36).
- I did not instantiate `Devlin55.BoundedSubsetAt`, so section 5's last claim is
  INFERRED at the module level and MEASURED at the type level.
- I did not measure that `⟪ Lset α ⟫ ↪ ⟪ α ⟫` fails to be a proposition.
- I did not touch `src/`, other tasks' directories, or any EXPECTED RED file.
  `agents/tasks/LJ-1-365/SoloC2.agda` is unchanged and still red at exit 42.
- I did not run `make check`.

## 12. FILES

All in `agents/tasks/LJ-1-368/`.

- `Probe368.agda` GREEN, the measurement.
- `MustFail368A.agda` EXPECTED RED, the tautology control.
- `MustFail368B.agda` EXPECTED RED, the true first data goal.
- `MustFail368C.agda` EXPECTED RED, the pinning control.
- `Floor368.agda` GREEN, the empty-file floor.
- `lj-1.368-report.md`, this file.
