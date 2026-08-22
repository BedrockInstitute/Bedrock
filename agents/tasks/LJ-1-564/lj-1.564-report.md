# LJ-1.564 report: PowerIntoSucc is built, and the bill behind it is five rows and not thirteen

## HEAD
head_slot: coder
machine: shared
task: LJ-1.564
obligation: agents/tasks/LJ-1-564/Probe564.agda::power-into-succ
verdict: GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-564/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. Nothing is postulated, the probe carries `--safe`, and there is no
hole. The probe is a raw `.agda` file, so it carries no ` ```agda ` fence,
counts 0 in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP EVENT.** The largest peak footprint of any run is 1,623,670,784
bytes, about 1.51 GiB, against an 8 GB cap
(`agents/tasks/LJ-1-564/runs/s6-1.out`). No run reported exit 251 and no run
printed a heap message.

## VERDICT

**GO. `power-into-succ` IS BUILT** at `agents/tasks/LJ-1-564/Probe564.agda:229`,
under TWO named hypotheses. The program's own meter agrees:
`scripts/pod/witness.py --brief` reports
`pass exit=0 3.32s agents/tasks/LJ-1-564/Probe564.agda::power-into-succ` and
`witness: 0 UNRESOLVED of 1, 3.32 s, probe_red=False`.

**READ THE GO WITH ITS SECOND HALF, AND THE SECOND HALF IS THE LARGER RESULT.**
The two hypotheses this term carries are NOT the price of the direction. They
are the price of ONE unbuilt code plus the condensation input. While measuring
that price I found that **FOUR of the rows every predecessor carried as a
hypothesis are theorems of the tree today**, and that **FOUR more are terms
other tasks already delivered**. Section 8 of the probe plugs all eight in, and
what is left of `GCHStatement` is FIVE named rows
(`agents/tasks/LJ-1-564/Probe564.agda:456-463`).

**NOBODY HAD ATTEMPTED THIS DIRECTION AND THE REASON IT LOOKED HARD IS GONE.**
`[LJ-1.550]` recorded R5 (`InclusionCoded`) and R6 (`InjLTrans`) as residues and
gave its reason in the file: "The only producers of `InjCode` in src/ are
src/L/Absorption.lagda.md:614 and src/L/CodedShift.lagda.md:40, and both deliver
the single shape `InjCode F (sucʟ γ) γ`" (`agents/tasks/LJ-1-550/Probe550.agda:322-323`),
and "src/L/CantorBernstein.lagda.md is the only consumer of `InjL` in src/ and
it delivers `mutual-inj→bijection` (:51-55), not transitivity"
(`Probe550.agda:329-331`). **BOTH SEARCHES MISSED `src/L/InjChain.lagda.md`,
AND THE REASON IS MECHANICAL.** That master produces the FOUR CONJUNCTS as
separate fields. It never writes the word `InjCode` at a producer site and it
never writes `InjL` at all, so a grep for either name cannot reach it. Its row 1
(`src/L/InjChain.lagda.md:313-434`) is the composite of two coded injections and
its row 3 (`src/L/InjChain.lagda.md:463-598`) is the inclusion of one set into
another, carved. Each delivers `sv`, `dm`, `ij` and `ran` at the exact frame
`InjCode` names (`src/L/Cardinal.lagda.md:223-228`).

## THE PRICE

All numbers at caliber `-A64m -I0 -M8g`, one Agda process at a time.

| run | what the file was | result |
|---|---|---|
| `runs/w3-1.out` to `runs/w3-3.out` | W3 ALONE, `runs/W3.agda`, 46 lines | exit 0, 1.45 s, 1.68 s, 1.64 s |
| `runs/s3-1.out` | sections 1 to 3 | exit 0, 1.48 s |
| `runs/s4-1.out` | the same with section 4, first form | exit 42, `[ParseError]`, "A type signature cannot have a where clause" |
| `runs/s4-2.out`, `runs/s4-3.out` | section 4 repaired, then split at the landing | exit 0, 1.54 s and 1.69 s |
| `runs/s5-1.out` | section 5, D-10 | exit 0, 1.73 s |
| `runs/s6-1.out` | section 6, which first imports `P550` and `P558` | exit 0, 9.05 s, 1.51 GiB |
| `runs/s7-1.out` | section 7 | exit 0, 6.23 s |
| `runs/s8-1.out` | section 8, which first imports `P528`, `P543`, `P540`, `P544` | exit 0, 29.31 s |
| `runs/final-1.out` to `runs/final-3.out` | **the file exactly as this report describes it**, 463 lines | exit 0, 7.04 s, 6.99 s, 7.18 s |

Every `final-*` run deleted `_build/2.8.0/agda/agents/tasks/LJ-1-564/Probe564.agdai`
first. The seven predecessor probe interfaces stay built across those three runs,
so 7.0 s is the price of THIS file and not of the chain under it. The `s6-1` and
`s8-1` numbers each include building the interfaces of the probes that run first
names, which is why they are larger than the run after them.

The probe is 463 lines, of which 184 are not a comment and not blank.

## WHAT IT COST AND UNDER WHAT

**THE TERM.** `agents/tasks/LJ-1-564/Probe564.agda:229-235`.

    power-into-succ :
        (zf : ModelL.isZFModel)
      → StageLanding zf → StageCountedCoded
      → (κ δ : SL.S) → SuccCardL δ κ
      → InjL (ModelL.isZFModel.𝒫 zf κ) δ
    power-into-succ zf land b9 κ δ sc =
      power-into-succ-from-landing zf b9 κ δ sc (land κ δ sc)

`power-into-succ-is-the-conjunct` (`Probe564.agda:241-244`) is the type check
that says this is `GCHStatement`'s second conjunct and not a neighbour of it: it
gives the same term the type `PowerIntoSucc zf`, which is `[LJ-1.558]`'s
hypothesis 2 (`agents/tasks/LJ-1-558/Probe558.agda:93-96`) copied letter for
letter.

**THE HYPOTHESES IN FULL. TWO, AND BOTH ARE MARKED NOT DISCHARGED.**

| # | hypothesis | at | state |
|---|---|---|---|
| 1 | `StageLanding zf` | `Probe564.agda:105-111` | **NOT DISCHARGED.** Every member of `𝒫 κ` lies in `Lset (fst δ)`. This is the bounded subset theorem at the use site, and it is `[LJ-1.558]`'s type (`Probe558.agda:59-64`), which is `[LJ-1.550]`'s `UseSite.member-in-stage` (`Probe550.agda:257-261`) |
| 2 | `StageCountedCoded` | `Probe564.agda:127-130` | **NOT DISCHARGED.** `InjL Lδ δ` where `fst Lδ ≡ Lset (fst δ)`. This is B9 (`agents/tasks/LJ-1-523/Probe523.agda:258-261`) |

**AND THE THREE THAT ARE NOT HYPOTHESES ANY MORE.** Each was a residue of
`[LJ-1.550]` and a hypothesis of `[LJ-1.558]`'s `stage-is-one-middle`
(`Probe558.agda:229-232`). Each is now a term of this probe, out of `src/`.

| row | type at | paid by | at |
|---|---|---|---|
| R4 `StageIsL` | `Probe564.agda:113-114` | `isL-Lset` | `src/L/Axioms/Basic.lagda.md:156` |
| R5 `InclusionCoded` | `Probe564.agda:117-120` | `L.InjChain.InclGraph` | `src/L/InjChain.lagda.md:575-598` |
| R6 `InjLTrans` | `Probe564.agda:123-124` | `L.InjChain.Comp` | `src/L/InjChain.lagda.md:314-434` |

R5 needed no conversion at all. `InclGraph`'s `sub` parameter
(`src/L/InjChain.lagda.md:576`) is `(z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩`,
and `𝒮ᵥ`'s `_∈ˢ_` IS `_∈_` (`src/V/Hierarchy.lagda.md:81`), so `InclusionCoded`'s
inclusion argument and `InclGraph`'s parameter are the same type. The three
terms together are 8 non-comment lines (`Probe564.agda:155-177`).

**THE SHAPE, AGAINST ITS PREDECESSOR.** `[LJ-1.550]`'s `bridge-with-residues`
(`Probe550.agda:335-339`) built the same arrow from THIRTEEN inputs. This term
builds the second conjunct from TWO.

## HOW FAR GCHStatement NOW IS

**THE BRIEF ORDERS A COUNT AND NOT AN ESTIMATE, SO THE ELABORATOR DID THE
COUNTING.** A count read off a table of other people's reports is still a
reading. Section 8 of the probe plugs every paid row into the slot this route
asks for, and a mismatch of one implicit would be exit 42.

**OF `[LJ-1.558]`'s THREE HYPOTHESES, TWO ARE PAID AFTER THIS TASK.**

| # | hypothesis of `[LJ-1.558]`'s route | state after this task |
|---|---|---|
| 1 | `SuccCardExists` | **PAID.** `[LJ-1.528]`, plugged at `Probe564.agda:439-440` |
| 2 | `PowerIntoSucc` | **PAID UNDER TWO NAMED ROWS**, this task, `Probe564.agda:229` |
| 3 | `SuccIntoPower` | **NOT PAID.** The twin. Not attempted here, as the brief orders |

**AND THE WHOLE REMAINING BILL FOR `GCHStatement` IS FIVE ROWS.**
`gch-from-five` (`Probe564.agda:456-463`) is the type check.

    gch-from-five :
        (zf : ModelL.isZFModel)
      → P550.AmbientCardAtSucc → P550.SqAt → P550.CoHyps
      → StageCountedCoded
      → P558.SuccIntoPower zf
      → GCHStatement zf

| # | row | what it is | who owes it |
|---|---|---|---|
| 1 | `AmbientCardAtSucc` | `(κ δ : SL.S) → SuccCardL δ κ → IsCardinal (fst δ)`, the AMBIENT cardinality at the successor | `[LJ-1.550]`'s R1 (`Probe550.agda:301-302`). `[LJ-1.550]` section 6 proves the site cannot be moved and B5 does not fill it |
| 2 | `SqAt` | the square law at `fst κ` | `[LJ-1.550]`'s R2 (`Probe550.agda:310-311`). `src/L/StageBound.lagda.md:42` says `SqCollect` is not inhabited |
| 3 | `CoHyps` | `levelIn` and `cover` over the telescope | `[LJ-1.550]`'s R3 (`Probe550.agda:215-230`), which is `Co`'s two parameters (`src/L/BoundedSubset.lagda.md:1555-1558`) |
| 4 | `StageCountedCoded` | `InjL Lδ δ`, the stage counted AS A CODE | B9. Its ambient shadow IS delivered: `stage-card-upper` (`src/L/StageCardinal.lagda.md:564-566`) |
| 5 | `SuccIntoPower` | `InjL δ (𝒫 κ)` | B10, the twin, blocked on a formula |

**EIGHT ROWS LEFT THE BILL AND HERE IS WHERE EACH WENT.** Four became theorems
of `src/`, four became terms other tasks delivered.

| row | left the bill because |
|---|---|
| `BoundedSubsetTheorem` | it IS `Devlin55.BoundedSubsetAt.Co.theorem`. `bounded-subset-theorem`, `Probe564.agda:397-405` |
| R4 `StageIsL` | `isL-Lset`, `src/L/Axioms/Basic.lagda.md:156` |
| R5 `InclusionCoded` | `L.InjChain.InclGraph`, `src/L/InjChain.lagda.md:575-598` |
| R6 `InjLTrans` | `L.InjChain.Comp`, `src/L/InjChain.lagda.md:314-434` |
| B4 `SuccCardExists` | `[LJ-1.528]`, `agents/tasks/LJ-1-528/Probe528.agda:696-697` |
| B6 `SubsetIntoStage` | `[LJ-1.543]`, `agents/tasks/LJ-1-543/Probe543.agda:125-130` |
| B7 `AbsorbsAt` | `[LJ-1.540]`, `agents/tasks/LJ-1-540/Probe540.agda:359-364` |
| B8 `LimitAbove` | `[LJ-1.544]`, `agents/tasks/LJ-1-544/Probe544.agda:225-228` |

**ONE WEAKENING WAS NEEDED AND IT IS FREE, AND THE NEXT BRIEF MUST KNOW IT.**
The producer of the bounded subset theorem's use site needs `IsOrd (fst κ)` and
`κ ∉ ω` (`Probe550.agda:232-237`), and `SuccCardL δ κ` carries neither
(`src/L/GCH.lagda.md:46-53`). `GCHStatement` binds both at its own head
(`src/L/GCH.lagda.md:60-62`), so a producer of the second conjunct may ask for
them. `PowerIntoSuccAt` (`Probe564.agda:327-332`) is `PowerIntoSucc` with those
two premises, and `gch-route-with-premised-hard` (`Probe564.agda:335-345`) is the
type check that says `[LJ-1.558]`'s route still closes with the weaker row in
hypothesis 2's place. It does not ask for `IsCardinalL κ`: the route does not
need it.

## D-10, BEFORE ANY AGDA

The brief orders this answered first, at `file:line`, and it was.

**QUESTION 1. DOES THIS ROW NEED THE BOUNDED SUBSET THEOREM AT ALL?**

**YES, AND THE ANSWER IS MECHANICAL AND NOT A READING.** `[LJ-1.543]` found that
a sibling row, B6, does not need the theorem and costs 9 lines
(`agents/tasks/LJ-1-543/Probe543.agda:125-130`). B6 is not an alternative to the
theorem. **B6 IS ONE OF THE THEOREM'S OWN INPUT SLOTS**, `x⊆Lα` at
`src/L/BoundedSubset.lagda.md:1390`. `t-x-slot` (`Probe564.agda:294-295`) is that
slot copied letter for letter, and `b6-fills-the-slot` (`Probe564.agda:299-304`)
is the one line that puts B6 in it. `[LJ-1.550]` already spends B6 exactly there
(`Probe550.agda:265`, `x⊆ = b6 κ y ordκ y∈`).

**THE DIFFERENCE IS WHICH OBJECT GETS PLACED, AND IT IS ONE STEP OF MEMBERSHIP.**
B6 places `z` where `z ∈ y ∈ 𝒫 κ`. Such a `z` is an ORDINAL BELOW κ, and the
tower places every such `z` with no theorem, which is why B6 is 9 lines.
`StageLanding` places `y` ITSELF, and `y` is a SUBSET of κ and not a member of
it. Nothing in the tower places a subset. That it appears below δ = κ⁺ is
Devlin 5.5 (`dev/literature/devlin-II5.md:147`), which is
`Devlin55.BoundedSubsetAt.Co.theorem : ⟨ x ∈ˢ Lset κ ⟩`
(`src/L/BoundedSubset.lagda.md:1621`).

**QUESTION 2. ARE `levelIn` AND `cover` DISCHARGEABLE HERE, OR MUST THEY BE
CARRIED?**

**THEY ARE CARRIED, AND I DID NOT TRY TO KILL THEM, AS THE BRIEF ORDERS.** They
are `Co`'s two parameters (`src/L/BoundedSubset.lagda.md:1555-1558`). They travel
as `CoHyps` (`Probe550.agda:215-230`) and they are row 3 of the five-row bill
above. **THEY ARE NOT THE TWO HYPOTHESES `power-into-succ` CARRIES.** The brief
guessed that they would be. What section 4's term carries is `StageLanding` and
`StageCountedCoded`; `levelIn` and `cover` are two of the SIX inputs that produce
`StageLanding`, and section 6 of the probe prices that reduction as a type.

**A CORRECTION TO THE BRIEF'S ARCHIVE PRICE, AND THE BRIEF'S OWN WARNING IS
RIGHT.** The brief prices the two as "a wall at 1.0k to 3.3k lines
(`archive/dev/LJ-dispatch-index.md:198`, `:222`)". Line 198 is `[LJ-1.121]`,
"priced 2.8k to 3.3k lines and not built". **THE NEXT LINE OF THE SAME TABLE
RE-PRICES IT.** `archive/dev/LJ-dispatch-index.md:199` is `[LJ-1.123]`,
"2.8k TO 3.3k BECAME 0.6k ... only the hull transfer remains". So the archive's
own record supersedes the upper half of the brief's range one line below the line
the brief cites. The brief is right that these are old prices at an old tree and
that nothing may be funded against them. I re-measured nothing here: this row
carries them and does not build them.

## W3, THE WIDEST UNMEASURED TERM

The brief names it: "whether `InjCode` can even be stated with `𝒫 κ` as its
source", and orders it written FIRST and typechecked ALONE. It was.
`agents/tasks/LJ-1-564/runs/W3.agda`, 46 lines, TYPE ONLY, no inhabitant,
exit 0 at 1.45 s, 1.68 s and 1.64 s (`runs/w3-1.out` to `runs/w3-3.out`).

**THE ANSWER IS YES AND IT IS FREE.** `CodeAtPower`
(`runs/W3.agda:36-38`, and `Probe564.agda:77-79` in the probe) states
`InjCode F (𝒫 κ) δ` and it elaborates with no coercion and no side condition.
The reason is one line each: `InjCode : S → S → S → Type (ℓ-suc ℓ)`
(`src/L/Cardinal.lagda.md:223`) and `𝒫 : S → S`
(`src/FOL/ZFModel.lagda.md:287`) are at the SAME `S`, the L-carrier's
(`src/L/GCH.lagda.md:27`). No constructibility premise about `𝒫 κ` is needed
either: `𝒫` is a field of `ModelL.isZFModel`, so its value is an L-element by
construction.

**THE BRIEF'S ESTIMATE WAS 12 LINES AND UNDER 60 SECONDS. MEASURED: 46 lines
and 1.45 s.** The extra lines are the import block and the comment; the
question itself is the three lines of `CodeAtPower`.

**AND THE ANSWER SHAPED THE ROW, AS `[LJ-1.546]` SAID IT WOULD FOR THE OTHER
DIRECTION.** Because the source slot is free, the row never needs a code built
AT `(𝒫 κ , δ)` from scratch. It needs a code at `(𝒫 κ , Lset δ)`, which is an
inclusion and which `src/L/InjChain.lagda.md` carves, and a code at
`(Lset δ , δ)`, which is B9.

## THE FOUR InjCode CONJUNCTS: DO THEY APPLY AT THIS PAIR

**NO. THEY ARE AT THE RANK CARVE AND NOT AT `(𝒫 κ , δ)`.**
`[LJ-1.559]`'s obligation is `domAt-at-carve : (a : S) (oa : IsOrd (fst a)) → DomAtOf (Carve.G a oa) a`
(`agents/tasks/LJ-1-559/Probe559.agda:336-339`), and the graph is
`Carve.G a oa` (`Probe559.agda:253`), the rank carve over an arbitrary
L-element `a`. `[LJ-1.524]`, `[LJ-1.529]` and `[LJ-1.531]` built the other
three at the same carve, and `[LJ-1.559]`'s report says the four are not at one
carve today.

**AND THIS ROW DOES NOT WANT THEM AT `(𝒫 κ , δ)`.** That is the finding, not a
complaint about the four. `src/L/InjChain.lagda.md` already produces all four
conjuncts at every inclusion (`:463-598`) and at every composite (`:314-434`),
so the pair `(𝒫 κ , δ)` is served the moment `(Lset δ , δ)` is served. **The
pair the campaign still needs a code at is `(Lset δ , δ)`, which is B9.** The
brief says `[LJ-1.566]` is assembling the four; this report's contribution to
that task is the target pair, and it is not the one in this brief's title.

## WHAT THE NEXT BRIEF NEEDS

1. **THE BILL IS FIVE ROWS AND `Probe564.agda:456-463` IS THE PROOF OF THAT
   NUMBER.** Do not re-derive it from reports. Import `LJ-1-564.Probe564` and
   read `gch-from-five`'s hypothesis list.
2. **B9 IS THE ONLY CODING ROW LEFT ON THE POWER SIDE**, and its pair is
   `(Lset δ , δ)`. Its ambient shadow is delivered
   (`src/L/StageCardinal.lagda.md:564-566`), so the gap is exactly
   ambient-injection to code at that pair.
3. **A PRODUCER OF THE SECOND CONJUNCT MAY ASK FOR `IsOrd (fst κ)` AND `κ ∉ ω`.**
   `gch-route-with-premised-hard` (`Probe564.agda:335-345`) proves the route
   still closes. A brief that states the conjunct without those two premises
   makes the bounded subset route unreachable for no gain.
4. **`src/L/InjChain.lagda.md` IS A PRODUCER OF `InjCode` AND NO GREP FOR
   `InjCode` OR `InjL` FINDS IT.** It produces the four conjuncts by their own
   names. Two predecessors recorded residues that this master already paid.
   Search for `svAt`, `domAt`, `injAt` and a range clause, not for the record
   type that packs them.

## WHAT I DID NOT DO

- I did not attempt `SuccIntoPower`. The brief forbids it and AD12 gives this
  brief one obligation.
- I did not discharge `levelIn` and `cover`. The brief forbids trying.
- I did not write into `src/`. I did not postulate. I did not commit or push.
- I did not write `review-of-power-into-succ.md`. That file states a stop, and
  this task is a GO.
- I did not re-measure the archive's line prices for the level-hood certificate.
  I report only what the archive's own rows say and that its two rows disagree.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED.** `:198` reads
  `| LJ-1.121 | Supply levelIn and cover at the site | NEITHER REFUTABLE, NEITHER SUPPLIED | The wall is the LJ-1.12 crossing, the level-hood certificate, priced 2.8k to 3.3k lines and not built |`
  and `:199` reads
  `| LJ-1.123 | Re-price the level-hood certificate | 2.8k TO 3.3k BECAME 0.6k | The LJ-1 series built the substrate under it; only the hull transfer remains. Read evidence, no probe |`.
  The second line is the correction to the brief's price range, reported under D-10.
- `archive/dev/JOURNAL-archived.md`: **not read.** Declined. The question of this
  task is which rows of a named bill are inhabited today, and that is settled by
  the tree and by the predecessor probes, not by a history of dispatches.
- `archive/dev/JOURNAL.md`: **not read.** Declined, for the same reason.
- `dev/ARCHIVE.md`: **not read.** Declined. Nothing was retired in this task, so
  there is no W4 row to write and no retired module to look up.
- `archive/dev/ORCHESTRATION.md`: **not read.** Declined. It is the archived
  rule set and the live rules reached me in the preamble.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ AND USED.** `:147` reads
  `> 5.5 Lemma. Assume V = L. Let κ be a cardinal. If x is a bounded subset of`.
  This is the statement behind `Devlin55.BoundedSubsetAt.Co.theorem` and it is
  the D-10 answer's source: the object that must be placed is the SUBSET, not a
  member of it.
- `dev/literature/truncation-and-selection.md`: **not read.** Declined. The one
  truncation step in this probe is `PT.rec2` into `InjL`, which is an hProp by
  `src/L/GCH.lagda.md:38`, so no selection question arises.
- `dev/literature/digest.md`: **not read.** Declined, not needed for this row.
- `dev/literature/geology.md`: **not read.** Declined, not needed for this row.
- `dev/literature/terms-2026-08.md`: **not read.** Declined. This task adds no
  term to `dev/glossary.toml` and proposes none.

## GATES

**ELEVEN CHECKS RAN AND EVERY ONE EXITS 0.** `lint-prose --check`,
`lint-agda --check`, `weave-i18n --check`, `check-glossary --check`,
`ledger --check`, `check-probes --check`, `check-closure --check closure`,
`check-fences --check`, `check-rule-ids`, `check-spec-surface --check` and
`reuse lint`.

**I DID NOT RUN `make typecheck`.** `git status --porcelain` shows one entry,
the untracked `agents/tasks/LJ-1-564/`, so no master changed and a whole-tree
typecheck would measure nothing about this task. The worktree carries no
`.venv`, so every gate ran as `/Users/alsg/Agentic/Bedrock/.venv/bin/python`,
the pinned interpreter of the main checkout, with the working directory left in
this worktree.

**THE WORKING TREE IS EXACTLY WHAT THIS REPORT DESCRIBES.** One untracked
directory, `agents/tasks/LJ-1-564/`, holding the brief, this report, the probe,
and `runs/` with the W3 slice, the run script and 14 run logs.
