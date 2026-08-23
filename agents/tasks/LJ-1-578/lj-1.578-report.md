# LJ-1.578 report: `CoHyps`, not supplied, and priced at a measured remainder

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO on `cohyps-supplied`; the remainder is ONE object with THREE clauses

Written as a skeleton before any Agda and filled as each answer landed (C-22).
No commit, no push. I wrote only inside `agents/tasks/LJ-1-578/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event. Nothing is postulated,
the probe carries `--safe`, and there is no hole. The probe is a raw `.agda`
file, so it carries no ` ```agda ` fence, counts 0 in-fence lines, and the ratio
bar cannot fire on it. Nothing lands in `src/`.

## VERDICT

**`CoHyps` IS NOT SUPPLIED, AND THE OBLIGATION IS NOT INHABITED.** The meter
says so: `runs/witness-1.out`, `1 UNRESOLVED of 1`, `probe_red=False`. The stop
is stated at `agents/tasks/LJ-1-578/review-of-cohyps-supplied.md`.

**AND THE REMAINDER IS NOW ONE OBJECT AND NOT THREE ITEMS.**
`certificate-gives-cohyps : Certificate → P550.CoHyps`
(`agents/tasks/LJ-1-578/Probe578.agda:547-549`), exit 0. `Certificate`
(`Probe578.agda:525-534`) is a formula that defines the level construction,
together with the fact that it does so in three readings: at the STAGE, for the
COVER, and in the COLLAPSE. **That object is the level-hood certificate, the
brief forbids me to build it, and I did not build it.**

**THE PRICE OF EVERYTHING ABOVE IT IS 176 LINES, MEASURED BY ME.** The
certificate's own three statements are 23 lines. Both counts are non-blank
non-comment lines of this probe, counted by me, and the table in
`## THE PRICE I MEASURED` breaks them down.

**THE BILL STILL HAS FIVE ROWS. IT DOES NOT HAVE FOUR.**

## D-10, THE INVENTORY I BUILD AGAINST

The brief orders D-10 before any Agda, against `[LJ-1.570]`'s inventory and not
against the archive's prose. This is what that inventory marks, at `file:line`.

| what | mark | where |
|---|---|---|
| `levelIn` | **NOT SUPPLIED, and not suppliable today** | `agents/tasks/LJ-1-570/lj-1.570-report.md:46` |
| `cover` | **NOT SUPPLIED, and not suppliable today** | `:78` |
| the down-reflection at arity n | **DELIVERED** at the seventeen-slot frame | `:58-61`, `Probe570.agda:233-249` |
| the hull's Skolem closure | machinery in `src/`, **no term at the site** | `:62-64`, `src/L/Hull.lagda.md:120` |
| the collapse iso | machinery in `src/`, **no term at the site** | `:62-64`, `src/L/BoundedSubset.lagda.md:152`, `:321` |
| the other three `[LJ-1.52]` survivors | **NOT BUILT ANYWHERE** | `:63-64` |
| `GraphAgree` | parts are terms in five probes, **none in `src/`** | `lj-1.570-report.md:96-100` |
| `HierInK` | **one open mathematical fact** | `:96-100`, `agents/tasks/LJ-1-532/Probe532.agda:274-277` |
| the hull re-basing | **no term exists** | `:96-100` |

**I BUILT AGAINST THESE MARKS AND ONE OF THEM MOVED.** The collapse iso is
marked "machinery in `src/` and no term at the site". The machinery is
`IsoInv` (`src/L/BoundedSubset.lagda.md:152`), its `iso-inv`
(`:195`) transfers satisfaction of EVERY formula across a collapse, and
`CollapseIso` (`:321`) already instantiates it at `:350`. **The term at the
site is now written**: `AtCollapse.iso-inv-at-the-site`
(`Probe578.agda:330-337`), 6 lines. The extensionality it wanted is
`HullExt.hullExt` (`src/L/BoundedSubset.lagda.md:1340`).

**I DID NOT RE-TEST WHETHER ROW 3 IS NEEDED AT ALL.** Premise 10 names
`[LJ-1.543]`'s finding that a sibling row was not needed. A measured cure does
not transfer by analogy (`AGENTS.md:45`), and re-measuring it here is a
different obligation from the one AD12 gave this brief. `[LJ-1.570]`'s
`row3-is-cohyps` (`Probe570.agda:110-116`) shows row 3 IS on the bill by
`gch-from-five`'s own type.

## WHAT I TOOK FROM LJ-1.570

**I IMPORTED IT. I DID NOT COPY IT.** `Probe578.agda:44` is
`import LJ-1-570.Probe570 {ℓ} lem as P570`, so a failure in that file is a
failure in this one.

| what I took | its lines in `Probe570.agda` | what I changed |
|---|---|---|
| `matrix-decode` and `adeq-decode`, the 41 measured lines | `:251-337` | **nothing.** Ascribed by use at `Probe578.agda:404-408` as `levels-decode` |
| `elem-down-at-the-site` | `:233-249` | **nothing.** Ascribed by use at `Probe578.agda:413-427` as `elem-down-taken` |
| `cohyps-at-today`, the seventeen-to-six reduction | `:188-194` | **nothing.** Consumed at `Probe578.agda:194-195` |
| `HullCondensation`, the six-slot statement | `:168-176` | **nothing.** It is `three-give-hull`'s target, `Probe578.agda:183` |
| `AtHull.LevelInH` and `AtHull.CoverH` | `:154-162` | **nothing.** They are `levelIn-from`'s and `cover-from`'s targets |
| `CoverAt`, the W3 type | `:84-96` | **nothing.** Restated at `Probe578.agda:67-82` and proved identical by `w3-is-570s`, `Probe578.agda:83-84` |
| `GraphAgree` and `Adeq` | `:289-294`, `:319-322` | **nothing.** They are `levels-decode`'s hypothesis and argument |

**THE 41 LINES ARE LIVE AT TODAY'S TREE AND I RE-MEASURED NOTHING ABOUT THEM.**
`levels-decode` typechecks (`runs/witness-2.out`, `0 UNRESOLVED of 7`), which is
what re-use buys. I did not recount the 41 and I do not restate that number as
mine.

## W3, THE WIDEST UNMEASURED TERM

**IT IS `cover`, AND THE MARK IS `[LJ-1.570]`'s OWN.** Two places say `cover`
is the harder of the pair:

- `lj-1.570-report.md:85-86`: `cover` asks for "the SAME adequacy as
  `levelIn`, on the level-MEMBERSHIP relation, plus a least-witness selection in
  the hull". Strictly more than `levelIn` asks.
- `lj-1.570-report.md:88-90`: "Unlike `levelIn` it is general at every
  consumer": three sites, none restricting the argument, against `levelIn`'s
  single consumer, which that report weakened to successors only
  (`Probe570.agda:360-365`).

**WRITTEN FIRST AND TYPECHECKED ALONE**, as the brief ordered:
`agents/tasks/LJ-1-578/runs/W3.agda`, 60 lines, **32 non-blank non-comment**.
`runs/w3-1.out` is exit 42 at the top-level module name. `runs/w3-2.out` is
**exit 0 at 3.70 s**. The slice was re-run after its comments were corrected, so
the first, cold run of the same slice has no record left and I do not quote its
figure. **The brief estimated about 12 lines under 90 seconds. The number is 32
lines and 3.70 s.**

## THE THREE FACTS, AND WHY THEY ARE THE SHARPENING

`[LJ-1.570]` cut `CoHyps` from seventeen slots to six and stopped with two whole
statements owing. **This task cuts the two statements to three facts, and NO
fact mentions the collapse's carrier `πX`.** That is the point of the cut:
`LevelInH` and `CoverH` both quantify over `HS.C.πX`, and `πX` is known to be a
stage only after `Condense` runs, which is what consumes them.

| fact | at `file:line` | what it says |
|---|---|---|
| A `HasLevels` | `Probe578.agda:120-122` | the hull is closed under the level construction |
| B `LevelsCommute` | `:126-128` | the collapse commutes with the level construction |
| C `Covered` | `:131-136` | every hull member sits inside a level indexed IN THE HULL |

**`levelIn` NEEDS A AND B. `cover` NEEDS B AND C, AND NOT A.**
`levelIn-from` (`:139-151`) and `cover-from` (`:153-169`). The collapse
machinery that carries them is delivered: `πX-member`, `πX-intro` and `π∈-fwd`
(`src/V/Collapse.lagda.md:78`, `:86`, `:102`).

**THEN FACTS A AND C ARE THE SAME SHAPE, AND THE SHAPE IS THE HULL'S OWN SKOLEM
CLOSURE** (`src/L/Hull.lagda.md:120`). `cert-gives-A` (`Probe578.agda:254-273`)
and `cert-gives-C` (`:275-298`) pay everything in them except the formula.
**FACT B IS THE SAME FORMULA READ A THIRD TIME**, and `b-from-across`
(`:513-522`) pays it through section 4's `iso-inv-at-the-site`.

**SO THE REMAINDER IS ONE OBJECT.** `Certificate` (`:525-534`).

**AND THE THREE CLAUSES ARE DEVLIN'S OWN CHAIN, SPLIT AT THE TREE'S JOINTS.**
Clause (i) is Devlin's (b) at `dev/literature/devlin-II5.md:99`. Clause (ii) is
the reverse inclusion's statement at `:107-108`. Clause (iii) is the collapse
transfer plus 1.9.15 at `:103-105`. **I did not choose the split from the
literature. I read the literature after the split typechecked, and it agrees.**

## THE REFLECTION STEP OF LJ-1.560

**`[LJ-1.570]` DID NOT TRY IT. MEASURED.** Its brief is not in the tree: `ls
agents/tasks/LJ-1-570/` returns four entries and none of them is `LJ-1.570.md`,
though `agents/tasks/LJ-1-570/review-of-cohyps.md:7` cites `LJ-1.570.md:9-12`. **So I cannot check what it was TOLD, and I
do not report that it was told anything.** What it DID is checkable.
`grep -rn "560\|search-bounds\|reflect" agents/tasks/LJ-1-570/` returns EIGHT
hits and not one of them is a reflection principle. **SIX are the string
"down-reflection"**, which is `DR54.ElemDown` and a different thing:
`Probe570.agda:136`; `lj-1.570-report.md:39`, `:59`, `:174`;
`review-of-cohyps.md:28`, `:46`. **The other two match on digits alone**:
`lj-1.570-report.md:70` matches inside the line reference "`:1560`", and
`runs/s1-2.out:24` matches inside the instruction count "34424385609".
**The strict grep settles it:
`grep -rn "LJ-1\.560\|LJ-1-560\|search-bounds\|mkReflect\|Single\.reflect\|Reflect\.lagda"
agents/tasks/LJ-1-570/` returns ZERO.**

**AND IT DOES NOT APPLY TO THE PAIR, FOR A REASON THAT IS A TYPE.**
`search-bounds` (`agents/tasks/LJ-1-560/Probe560.agda:165-176`) takes a FORMULA
and returns a STAGE at which its unbounded existential is answered.
`levelIn` and `cover` do not quantify over a stage. They quantify over
`HS.C.πX`. The one thing in the tree that identifies that carrier with a stage
is `Condense.condenses` (`src/L/BoundedSubset.lagda.md:1033`), **and it consumes
the pair**. `Circle.pair-gives-stage` (`Probe578.agda:378-380`) is that
consumption written as a term, so the circle is closed in Agda and not in prose.

**WHERE THE REFLECTION STEP WOULD APPLY IS INSIDE THE CERTIFICATE**, at clause
(i), which is a Σ₁ statement bounded to a stage. That is the level-hood
certificate and this brief does not fund it.

**THE CONVERSE IS OPEN AND I DO NOT CLAIM IT.** `Circle.StageGivesPair`
(`Probe578.agda:386-389`) is a TYPE with no inhabitant. I did not try to build
it and I do not assert it is true at this frame.

## THE PRICE I MEASURED

**EVERY NUMBER BELOW IS MINE, COUNTED BY ME OVER THIS PROBE, AND NONE IS
INHERITED.** Non-blank non-comment lines.

| what | lines | at `file:line` |
|---|---:|---|
| the three facts, STATEMENTS | **12** | `Probe578.agda:120-136` |
| `levelIn-from` and `cover-from`, TERMS | **27** | `:139-169` |
| `ThreeFacts` and its reduction to `CoHyps` | **26** | `:172-204` |
| certificate clauses (i) and (ii), STATEMENTS | **15** | `:234-251` |
| `cert-gives-A` and `cert-gives-C`, TERMS | **42** | `:254-298` |
| the collapse transfer at the site, TERM | **6** | `:330-337` |
| certificate clause (iii), STATEMENT | **8** | `:503-510` |
| `b-from-across`, TERM | **10** | `:513-522` |
| `Certificate` and its reduction to the bill | **28** | `:525-557` |
| **the whole remainder, as STATEMENTS** | **23** | clauses (i), (ii), (iii) |
| **everything paid ABOVE the remainder** | **176** | the rest of the probe |

**WHAT I DID NOT MEASURE, AND SAY SO.** I did not price the PROOF of any
clause of the certificate. 23 lines is the cost of STATING the remainder at
today's tree; it is not the cost of discharging it. **A brief funded against 23
lines would be funded against the wrong number, and this report does not offer
that number as a build price.**

**WHAT THE CERTIFICATE MUST CONSUME, MEASURED IN `src/`.** Counted by me,
non-blank non-comment lines inside the fences.

| module | lines | at `file:line` |
|---|---:|---|
| `LevelHood`, the formula itself | **65** | `src/L/BoundedSubset.lagda.md:74-147` |
| `LevelHood0`, the formula at zero | **19** | `:840-869` |
| `IsoInv`, delivered and now consumed | **158** | `:152-320` |
| `CollapseIso` | **22** | `:321-355` |
| `HullExt` | **91** | `:1235-1345` |

**`LevelHood` AND `LevelHood0` HAVE NO CONSUMER IN `src/` TODAY.** MEASURED by
`grep -rn "LevelHood" src/`, which returns three lines and every one is inside
the two modules' own definitions (`:74`, `:840`, `:844`). **The formula is
built. Nothing in `src/` says what it means.** That is the certificate's gap in
one measurement.

**AGAINST THE ARCHIVE'S TWO NUMBERS.** `[LJ-1.121]`'s "2.8k to 3.3k lines"
(`archive/dev/LJ-dispatch-index.md:198`) and `[LJ-1.146]`'s "about 1.0k lines"
(`:222`) **are not confirmed and not refuted by this task, and nothing here is
funded against either.** What this task measured is that the SHAPE has changed
again: at `[LJ-1.146]` the pair was two open statements, at `[LJ-1.570]` it was
three items, and today it is one object with three clauses and 176 lines already
paid above it.

### Seconds and lines for the probe

Three forced rechecks, the interface removed before each, one Agda process, all
exit 0: **20.04 s, 19.99 s, 20.29 s** (`runs/final-1.out` to `runs/final-3.out`),
**median 20.04 s**, peak 2,493,874,176 bytes, about 2.32 GiB against the 8 GB
cap. **No heap event, and the resident set is under a third of the cap.**
`runs/final-4.out` is a fourth run of the same file, kept because it is the run
that first followed the comment corrections; it is exit 0 at 19.32 s and no
number in this report is taken from it.

`Probe578.agda` is 557 lines, **313 non-blank non-comment**. By section:
imports and header 28, section 1 (W3) 16, section 2 (the three facts) 72,
section 3 (the certificate at the stage) 66, section 4 (the collapse transfer)
16, section 5 (the circle) 14, section 6 (what I took) 21, section 7 (the
remainder) 25, section 8 (fact B) 55.

**THE BRIEF ESTIMATED ABOUT 190 LINES WITH THE OBLIGATION AT ABOUT 50. THE FILE
IS 313 AND THE OBLIGATION IS ABSENT.** The 123 lines above the estimate are
sections 3 and 8, which the brief did not ask for: they are what turned three
items into one object.

### Gates

`check-probes.py --check` clean, 6,875 tracked files. `lint-agda.py --check`,
`lint-prose.py --check`, `check-fences.py --check` and `check-glossary.py
--check` all exit 0. I did not run `make check`: I commit nothing.

## WHAT THIS DOES TO THE BILL

**ROW 3 IS NOT PAID. THE BILL IS STILL FIVE ROWS.**
`agents/tasks/LJ-1-550/Probe550.agda:215` is row 3 and
`agents/tasks/LJ-1-564/Probe564.agda:456` is the five.

| row | what this task did to it |
|---|---|
| 1 `AmbientCardAtSucc` | **NOT ATTEMPTED.** AD12 gives this brief one obligation. |
| 2 `SqAt` | **NOT ATTEMPTED.** |
| **3 `CoHyps`** | **NOT PAID.** Reduced to ONE object with three clauses, 176 lines paid above it. |
| 4 `StageCountedCoded` | **NOT ATTEMPTED.** |
| 5 `SuccIntoPower` | **NOT ATTEMPTED.** |

**I DO NOT READ A DISCHARGE INTO ANYTHING I DID NOT INHABIT.** No term in this
probe has type `P550.CoHyps`. Every term that mentions `CoHyps` is an
implication with a named hypothesis: `three-give-cohyps` takes `ThreeFacts`,
`remainder-gives-cohyps` takes `Remainder`, `certificate-gives-cohyps` takes
`Certificate`. **None of the three hypotheses is inhabited anywhere.**

## WHAT THE SHAPE RESISTED

**ALMOST NOTHING RESISTED, AND THAT IS THE FINDING.** Sections 2, 3, 4 and 8
each typechecked at the FIRST attempt. The only two failures on the whole task
were scope errors: `L.Constructible.𝒮ʟ` written as a qualified name instead of
imported (`runs/s1-1.out`, `runs/s6-1.out`) and `mapFo` sought in
`FOL.Syntax` when it lives in `FOL.Manipulation.Relabelling:54`
(`runs/s4-1.out`).

**WHAT THAT MEANS FOR THE NEXT BRIEF.** The joints of this chain are already
cut in `src/`. `πX-member`, `πX-intro`, `π∈-fwd`, `closed`, `hull-member`,
`iso-inv`, `hullExt` and `condenses` all fit together with no glue beyond
`subst` and `PT.rec`. **Four hundred dispatches of wall at this pair were not a
wall in the plumbing. Every line of resistance is in the one formula whose
meaning nothing states.**

**WHAT I COULD NOT CLOSE.** The three clauses of `Certificate`.
`StageGivesPair`. Nothing else: the obligation is absent, and no part of it is
weakened, hidden or postulated.

## WHAT THE NEXT BRIEF NEEDS

- **Brief the certificate as ONE task with THREE clauses, not as three items.**
  `Probe578.agda:525-534` is the type. Clause (i) is the one to attack first:
  clauses (ii) and (iii) reuse its formula, and `cert-gives-C` and
  `b-from-across` already consume them.
- **Clause (i) is Devlin's (b) and nothing more**
  (`dev/literature/devlin-II5.md:99`). It is stated over the hull's META term
  algebra and not over object formulas, which is DD27's ruling
  (`archive/dev/DD-archived.md:37`), so a brief that asks for a
  `Formula CS.S 4` has asked at the wrong carrier.
- **`LevelHood` has no consumer in `src/` and that is where the campaign's
  cost sits.** `grep -rn "LevelHood" src/` returns three self-references.
  A task that gives it its first consumer is worth more than a task that
  restates the pair.
- **The seventeen-slot frame is worth more than the six for a supplier.**
  `elem-down` is delivered there and not at the six
  (`lj-1.570-report.md:37-42`, `Probe578.agda:413-427`). My three facts are
  stated at the six, which is stronger; a supplier that needs `elem-down` should
  take the wider frame and lose nothing, because `cohyps-at-today` bridges the
  two (`Probe570.agda:188-194`).
- **`StageGivesPair` is worth five minutes of D-10 before it is briefed.**
  If it is true, the pair and the condensation equation are the same request and
  `[LJ-1.536]`'s parked residue may join them. **This report does not prove it
  and does not claim it.**

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` — **READ**, rows 198 and 222. `:222` reads
  "| LJ-1.146 | Price levelIn and cover, the root of the unconsumed chain | A WALL, NAMED TWICE AT ONE TERM | The trophy needs them. About 1.0k lines. C-35 fires wing-wide, the trophy is unwritten |".
  TOOK the two archived prices as SHAPE only. Nothing in this report is funded
  against either, and `## THE PRICE I MEASURED` says so in writing.
- `archive/dev/JOURNAL.md` — **READ**, `:410`, which reads
  "level-hood must run through codes and satisfaction, and those leaves are".
  TOOK the reason the level story is expensive on this tower at all, which is
  why the remainder is a formula's certificate and not a set-theoretic lemma.
- `archive/dev/DD-archived.md` — **READ**, `:37`, which reads
  "| DD27 | **THE HULL IS INDEXED BY A META TERM ALGEBRA, not by object-language formulas.**".
  TOOK the warrant for stating certificate clauses (i) and (ii) over
  `T.Code` rather than over `Formula CS.S 4`. Without DD27 the clauses would
  have been written at the wrong carrier and `closed` would not have applied.
- `archive/dev/JOURNAL-archived.md` — **READ**, `:723`, which reads
  "(zero hits for Tarski/Vaught/hull/cardinal machinery anywhere in src); a new".
  TOOK the record that the hull was greenfield when the campaign began. It is
  the measurement this task's `## WHAT THE SHAPE RESISTED` is set against: the
  machinery that was absent then is what fits together with no glue today.
- `archive/dev/PLAN-archived.md` — **NOT USED. DECLINED.** Grepped for
  `levelIn`, `cover` and `condensation`; the two hits are about task-registry
  bookkeeping and the `L7.2` exclusion sweep, neither of which bears on this
  pair. Its own header at `:1` says "# ARCHIVED 2026-08-20" and `:4` says
  "Nothing below is current."

## LITERATURE USED

- `dev/literature/devlin-II5.md` — **READ**, `:95-110`. `:99` reads
  "> (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)].".
  TOOK the identification of certificate clause (i) with Devlin's (b), of
  clause (ii) with the reverse inclusion at `:107-108`, and of clause (iii)
  with the collapse transfer at `:103-105`. **I read this AFTER the split
  typechecked, so the agreement is a check and not a design input.**
- `dev/literature/truncation-and-selection.md` — **READ**, `:17`, which reads
  "LEAST witness under a definable well-order, and all three write leastness with".
  TOOK the decision NOT to require uniqueness in clause (ii)
  (`Probe578.agda:244-251`): the classical sources select a LEAST witness, and
  the hull's `search` already does that selection
  (`src/L/Hull.lagda.md:79-81`), so a supplier owes no leastness clause of its
  own. Clause (i) does require uniqueness, because the level at an ordinal is
  unique and `cert-gives-A` uses that.
- `dev/literature/level-formula-slot-roles.md` — **READ**, `:9`, which reads
  "arithmetic**, and a port that numbers its variables needs the slot arithmetic.".
  TOOK the warning that a port must re-derive the slot roles. This task did NOT
  re-derive them and did not need to: it IMPORTS `[LJ-1.570]`'s already
  corrected assembly (`Probe578.agda:404-408`) instead of porting it again.
  **The digest is why the import is the right move and a copy is not.**
- `dev/literature/digest.md` — **NOT USED. DECLINED.** `devlin-II5.md:18-20`
  records that the digest's Devlin II.5 entry carries no part of the chain, so
  it is the fetch record and not content. `[LJ-1.570]` declined it for the same
  reason and I did not pay the reading twice.
- `dev/literature/geology.md` — **NOT USED. DECLINED.** Set-theoretic geology
  bears on no step of the condensation transfer, on the hull's Skolem closure,
  or on the level formula. Nothing in this task touched it.
