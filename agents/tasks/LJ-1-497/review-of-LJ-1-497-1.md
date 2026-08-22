# LJ-1.497 review: adversarial review of the LJ-1.497#1 return

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

## WHAT I ATTACKED, AND WHAT I DID NOT TAKE ON TRUST

The return under attack is `agents/tasks/LJ-1-497/lj-1.497-report.md`, the
newest `*-report.md`. The author is the coder head. I am the
mathematician_adversarial head, so the invariant holds: the critic is not the
author. Two earlier critic dispatches existed (`review-LJ-1-497-1.md`,
`review-LJ-1-497-2.md`, head_slot coder_adversarial) and wrote nothing; no
`review-of-` file existed before this one.

I did not accept the return's runs on trust. I re-ran the load-bearing parts:

1. **Cold recheck, today.** I deleted the interface
   `_build/2.8.0/agda/agents/tasks/LJ-1-497/Probe497.agdai` and ran Agda on
   `agents/tasks/LJ-1-497/Probe497.agda` at the same caliber
   (`GHCRTS=-A64m -I0 -M8g`). Exit 0, 2.67 s. The reported full-file median is
   2.67 s (`runs/full-2.out`, `runs/full-3.out`, `runs/full-4.out`). The whole
   file is green today, not only on the day of the return.
2. **Vacuity.** `no-adequacy` (`Probe497.agda:435-451`) carries hypotheses
   `a`, `oa`, `m`, `mx`. They are inhabited: take `a` as the wrap of
   `sucV ∅`, `oa` as `suc-ord ∅-ord`, `m` as `∅ˢ` (`Probe497.agda:338`), and
   `mx` from the membership that `sucV` supplies. The accept arm recorded
   `agda_vacuous: false` (`runs/accept-1.out`). The refutation is not a term
   over a dead hypothesis.
3. **Faithfulness of the rebuild.** The padding and the whole-carrier index
   are not inventions of this return. `Probe416.agda:57-58` pads `eq` and `gt`
   with `∅ , ∅-ord`; `Probe416.agda:72` takes `boundingOrd A` over the whole
   carrier; `Probe490.agda:134-135` and `:145` carry the same lines;
   `Probe497.agda:93-96` restates them with `bnd` named. The refuted rank is
   the rank the campaign delivered at `[LJ-1.416]` and rebuilt at
   `[LJ-1.490]`. It is not a strawman.
4. **The chain (a) to (d).** I read each term. (b) `fn-no-pairs`
   (`Probe497.agda:299-312`) turns a `q`-minimal `m` into a pair-free `f`
   through `inDomAt-adequate` and `appAt-adequate`. (a) `sup-no-member`
   (`Probe497.agda:329-334`, resting on `body-absurd` at `:315-326`) uses
   `extAt-out` on the biconditional `extAt` (`src/L/Coding/Model.lagda.md:662-664`)
   to pin `r` memberless at a pair-free `f`. The witness block
   `Sat` (`Probe497.agda:380-428`) builds a satisfaction of `rankFo ∅ˢ a` at
   `pr m ∅`. (d) `no-adequacy` feeds that satisfaction to the adequacy,
   extracts `∅ ≡ swo-rank …` with `pr-inj` (`src/V/Coding.lagda.md:178`), and
   refutes it with `rank-at-has-∅` (`Probe497.agda:213-216`), itself a
   consequence of `pred-self` (`:117-122`, trichotomy at a point against
   itself is never `lt` and never `gt`) and `step-mem` (`:98-101`). Every link
   is a term in a file that typechecks.
5. **The obligation is still open.** The program's own witness file resolves
   `Target.rankFo-adequate` against the probe
   (`.pod-state/witness/Witness-LJ-1-497-65e8c9c5.agda:16`), and the accept
   facts record `obligations_open: 1`, `obligations_delta: 0`
   (`runs/accept-1.out`). This is what the closing row requires.

## QUESTION 1: DOES THE VERDICT LINE MATCH ITS OWN BODY

**Yes.** The line claims: NO-GO; the statement is FALSE, not merely unbuilt;
a refutation that typechecks; the whole file green.

- The term `no-adequacy` exists at exactly `Probe497.agda:435-451` in a file
  of 451 lines, with the type the line quotes. The file typechecks cold
  today (my recheck above).
- "The statement is FALSE" is true for the statement as the brief telescoped
  it. The obligation block of `LJ-1.497.md` writes `(Q a z : S)` and puts no
  hypothesis on `Q`. A universally quantified `Q` is refuted at one `Q`, and
  the return refutes it at `Q := ∅` with a constructed satisfaction
  (`Probe497.agda:425-428`).
- The body does not hide the soft spot. It names the `Q := ∅` degeneracy
  itself, separates the unconditional (d) from the `Q`-independent content
  (a) plus (c) plus `rank-at-has-∅`, and names the one unbuilt step (a
  well-order has a minimal member of `a`, which needs `Q` read as an `SWO`).
  The line does not outrun the body.
- The brief predicted a NO-GO "would retire `[LJ-1.475]`'s formula". The body
  says the opposite of that prediction, with a reading of the formula
  (`ρ(m) = sup{ρ(y)+1 : y < m}`) that the D-10 table supports clause by
  clause. A return that corrects the brief's prediction, and says so, is a
  match between line and body, not a defect.
- The slot attribution is exact. The inner `∃̇` of `Probe497.agda:258` is the
  third existential; its witness is `r` (env `f ∷ r ∷ m ∷ q ∷ z`);
  `prAtL (s3 zero) (suc zero) zero` at `:259` reads `z` as the pair of `m`
  and `r`; `supAt zero (suc zero)` at `:263` pins it. That is the slot the
  range clause reads (`agents/tasks/LJ-1-490/Probe490.agda:280`).

**Did the BRIEF cause the outcome?** No. The divergence is forced by the
delivered code (`Probe416.agda:57-58`, `:72`), not by the brief's wording.
The brief's own D-10 instruction made the divergence a sanctioned deliverable
("STOP AND SAY WHICH SLOT DIVERGES"). The one defect the brief did carry, the
missing `oa`, the return repairs with the predecessor's hypothesis
(`Probe490.agda:211`, `module Bound (a : S) (oa : IsOrd (fst a))`), and it
declares the repair at `lj-1.497-report.md:243-246`. The brief also left `Q`
unhypothized; the return turns that gap into a finding
(`lj-1.497-report.md:221-225`) rather than exploiting it silently.

## QUESTION 2: IS EVERY LOAD-BEARING CLAIM BACKED BY A file:line THAT RESOLVES TODAY

**Yes.** I resolved every citation the return rests on:

- Inside `Probe497.agda`: `:74-135` (the rank module), `:93-96`, `:98-101`,
  `:121-125`, `:203-208`, `:213-216`, `:225-229`, `:231-239`, `:241-250`,
  `:252-253`, `:255-263`, `:275-280`, `:299-312`, `:315-326`, `:329-334`,
  `:351-362`, `:365-368`, `:425-428`, `:435-451`. All exact.
- Inside `Probe490.agda`: `:95-96` (`rankFo`), `:105-109` (`rank-graph`),
  `:111-114` (`rank-graph-out`), `:123-157` (the rank), `:134-135` (the
  padding), `:145` (`boundingOrd A` over the whole carrier), `:147-148`
  (`swo-rank`), `:165-201` (`OrdSWO`), `:167-168` (the `∈ᵗ`-valued order at
  `Type (ℓ-suc ℓ)`), `:211-213` (`oa` and `pack`), `:216-217` (`C`), `:280`
  (`⟨ fst y ∈ fst B.C ⟩`). All exact. The 490 report itself carried line-cite
  defects; this return carries none that I found.
- In `src/`: `src/L/Ordinal.lagda.md:154` (the `boundingOrd` signature),
  `:156-167` (`β = ⋃ (sett X g)` with `g x = sucV (f x)`);
  `src/L/Coding/Model.lagda.md:662-664` (`extAt`, two implications conjoined);
  `src/V/Coding.lagda.md:178` (`pr-inj`);
  `src/L/Constructible.lagda.md:46` (`∈∈ₛ`). All exact.
- Predecessor records: `agents/tasks/LJ-1-475/lj-1.475-report.md:107` ("GO.
  W3 typechecks `fn-clause`") and `:249` ("a well-order from the set `Q`,
  which this formula does not read"); `agents/tasks/LJ-1-490/lj-1.490-report.md:80-86`
  (the NO-GO verdict), `:271-272` (`b` determined, codomain `C`),
  `:275-279` (the other three conjuncts), `:281` ("Fund that bridge first");
  `agents/tasks/LJ-1-490/review-of-LJ-1-490-1.md:194` (upheld, same order of
  work). All exact.
- The runs. All twelve files exist. `runs/w3-1.out` through `w3-3.out`: 1.80,
  1.72, 1.85 s, peak 295141376, 295108608, 295141376 bytes, exit 0, so the
  reported median 1.80 s and peak 295141376 bytes are right.
  `runs/full-1.out` through `full-4.out`: 2.72, 2.67, 2.66, 2.67 s, peak
  358219776 bytes on three of four, exit 0, so the reported median 2.67 s and
  peak 358219776 bytes are right. `runs/cure-level.out` carries exactly the
  quoted `[UnequalSorts]` text and `exit=42`. `runs/cure-small.out` carries
  `exit=0`.
- The C-42 sweep. I re-ran it. `grep -rn boundingOrd src` gives 26 matches in
  11 files. The nine call sites resolve at the exact cited lines:
  `L/Reflect.lagda.md:447`, `L/InjChain.lagda.md:82`,
  `L/Recursion.lagda.md:136`, `L/Axioms/Full.lagda.md:222`,
  `L/Axioms/Basic.lagda.md:403`, `L/Axioms/Separation.lagda.md:537`,
  `L/Axioms/Power.lagda.md:147`, `L/Choice/Before.lagda.md:1015`,
  `L/Coding/EnvSet.lagda.md:95`. The two `Everything.lagda.md` prose hits and
  the prose line at `L/InjChain.lagda.md:69` resolve. Nine call sites plus
  nine import lines plus five in `L/Ordinal.lagda.md` plus two plus one is
  26. The arithmetic closes.
- The archive and literature quotes the return uses resolve:
  `archive/dev/JOURNAL-archived.md:3635` and
  `dev/literature/truncation-and-selection.md:28` (see my blocks below).

Three things do not resolve, and I state them at their weight:

1. **The transitions record my brief names does not exist.** My brief told me
   to read the six facts, `model`, `effort` and `heads_sha256` of this
   instance in `dev/pod/transitions/`. `dev/pod/transitions/2026-08.jsonl`
   holds 157 lines; its last entry is seq 158, task `LJ-1.399`, ts
   `2026-08-19T13:31:57Z`; no line contains `497`. The nearest records are
   the task's own `.pod` line (`agents/tasks/LJ-1-497/.pod:1`, heads
   `0a6fdffa…`, at `2026-08-21T20:47:34Z`) and the accept-arm facts in
   `runs/accept-1.out` (exit_code 0, heap_wall false, lines 0,
   obligations_delta 0, obligations_open 1, seconds 1.62; no `model`, no
   `effort`). The return makes no claim about that file, so no claim of the
   return fails. The gap is in the record the program keeps, not in the
   return, and the program should mend its log.
2. **The 194-line W3-only file was not preserved.** The claim "typechecked
   ALONE ... at 194 lines" has no artifact. The three `runs/w3-*.out` files
   exist, and their peak RSS (295141376 bytes) sits below the full file's
   (358219776 bytes), which fits a smaller file. The W3 finding is re-proved
   inside the full file (`Probe497.agda:203-216`), which I rechecked, so
   nothing rests on the unpreserved copy.
3. **The 143-line figure for the refutation chain does not reproduce.** I
   count 63 lines for the four cited blocks (`:299-312`, `:315-334`,
   `:351-362`, `:435-451`), and 112 with the `Sat` module (`:380-428`) that
   (d) rests on. Neither is 143. The figure feeds no price, so I record it
   and move on.

## QUESTION 3: IS THE PREDECESSOR'S ENUMERATION COMPLETE

**One measured gap, which corrects a count and moves nothing else.**

**The gap: the C-42 count stopped at `src/`.** C-42 asks for the count of the
shape in the tree before the cure is priced. The return counted `src/` (26
matches, 11 files, exposure 0; I reproduced all of it) and then wrote "The
defect has not reached the tree." The tree also holds the probe lineage, and
there the shape is present. My grep over `agents/tasks` gives five files that
carry `swo-rank`: `Probe416.agda`, `Probe417.agda`, `Probe486.agda`,
`Probe490.agda`, `Probe497.agda`. Two of the five are consumer sites, not
mere definitions: `Probe417.agda:83` (`pack = boundingOrd A swo-rank
swo-rank-ord`) and `Probe490.agda:213` (`pack = boundingOrd ⟪ fst a ⟫
(swo-rank w) (swo-rank-ord w)`), and 490's `pack` is the codomain `C` of the
range clause (`Probe490.agda:216-217`). So the corrected count is: 5 probe
sites, 2 of them consuming the defective rank today, 0 sites in `src/`. The
sentence "has not reached the tree" is true only with "tree" read as `src/`.
The return knew the lineage (its W4 paragraph says the rank "lives in a
probe, not in a module of `src/`"); what is missing is the COUNT. I record it
here so the next brief does not inherit the understatement. The verdict and
the named next brief do not move: an oversized `C` still bounds, the range
clause's falsity was `[UnequalTerms]`, and the return already says the cure
is one term, not four.

**Two minor records, kept at their weight:**

- The probe's header comment is stale. `Probe497.agda:2-4` says "The
  obligation is omitted here; this file is the W3 alone." The file holds the
  obligation as a type (`:275-280`) and the refutation (`:435-451`). A reader
  of the header alone would mis-scope the file. The report describes the
  file's content correctly, so nothing load-bearing rests on the comment.
- Section 3(c) compresses one step. It says `divergence` contradicts "the
  adequacy conclusion". The term's own hypothesis is
  `fst r ≡ fst (rank-at a oa m mx)` at the SAME `m` (`Probe497.agda:351-358`),
  while the adequacy conclusion quantifies its member existentially. The
  relocation through `pr-inj` is built in (d), not in (c). The return never
  claims (c) alone closes the `Q`-independent case, and it names the missing
  step itself, so this is prose compression, not a false claim.

**Everything else enumerates.** The D-10 table covers all six conjuncts of
`rankFo` (I read the formula at `Probe497.agda:255-263` and count the same
six). The four measurements are enumerated with the degeneracy declared. The
two definitional refactors are declared (`step` at `:93-96`, the
`supB2`/`supB1`/`supBody` split at `:241-250`). The required section
`## WHAT THE RANGE CLAUSE NEEDS NEXT` is present and answers both questions
the work brief named: `b` is determined (`lj-1.490-report.md:271-272`), and
what remains is a replacement rank, typed in the report. W2 is answered at a
generic carrier; no stage, cardinal, numeral or `Lset` is named. The three
accept-arm runs (`runs/accept-1.out` through `accept-3.out`) are unmentioned
in the report; they are program-side artifacts, not worker runs, so their
absence is not a defect of the return.

**The W3 channel held.** The work brief named the term (`rank-at`) and the
probe; the coder wrote and ran it (`Probe497.agda:203-216`,
`runs/w3-1.out` through `w3-3.out`). Per amendment A21, that is the whole
duty, and it was met.

**No cheaper cure was missed.** The two measured cure facts are the universe
error (`runs/cure-level.out`, exit 42) and the small membership
(`runs/cure-small.out`, exit 0). Alternatives I checked: a resized index
needs machinery this tree has not delivered; an `∈`-recursion at `V` that
bypasses `SWO` would be a new bridge with its own adequacy question, and the
delivered consumer (`Probe490.agda:213`) is typed at the `SWO` route. The
named cure, re-base the order on `_∈ₛ_` and then build `swo-rank′` over the
predecessors, is the cheapest measured route. The return prices nothing
beyond the two measured facts, which is the right discipline.

## VERDICT

**Upheld.** The NO-GO is correct on its own numbers. The measurement is
sound, faithful to the delivered code, and it reproduces today under my own
cold recheck. Every load-bearing claim is backed by a `file:line` that
resolves today. The one enumeration gap I found (the C-42 lineage count) is
corrected above and changes neither the verdict nor the next brief. The
statement as briefed is false, the divergence sits in the rank and not in
the formula, and the successor work is a replacement rank behind a
re-based order. Row `sys-critic-upheld-no-go`: this file, exit 0, and the
obligation still open. I write no table row.

## THE WORKING TREE

I wrote this file and nothing else. My cold recheck regenerated
`_build/2.8.0/agda/agents/tasks/LJ-1-497/Probe497.agdai` under the
git-ignored `_build/`; that interface already existed, from the accept arm,
before I deleted and regenerated it. `git status --porcelain` shows only
`?? agents/tasks/LJ-1-497/`. Nothing was committed and nothing was pushed.

## ARCHIVE USED

- `dev/ARCHIVE.md:1`
  "# ARCHIVE.md: the archive registry"
  Head read, then **declined**. This review retires no module, and the task
  under review retired none. The registry adds nothing to the three
  questions.
- `archive/dev/JOURNAL.md:1`
  "# ARCHIVED 2026-08-20"
  Head read, then **declined**. The journal is retired and its own head says
  the task directories carry the record. The record I needed is live, under
  `agents/tasks/LJ-1-497/`.
- `archive/dev/ORCHESTRATION.md:1`
  "# ORCHESTRATION: the orchestrator's operating rules"
  Head read, then **declined**. The retired orchestrator's rules do not bear
  on the value of a rank recursion.
- `archive/dev/DD-archived.md:1`
  "# THE `DD` RULING SERIES, archived in full 2026-08-18"
  Head read, then **declined**. No DD ruling bears on the three questions.
  The clauses that bind this review are live in `AGENTS.md` and in the slot
  file.
- `archive/dev/PLAN-archived.md:1`
  "# ARCHIVED 2026-08-20"
  Head read, then **declined**. The retired plan does not bear on the
  divergence measured here.
- Not a candidate; read to verify the return's load-bearing archive claim:
  `archive/dev/JOURNAL-archived.md:3635`
  "  (`L.OrdinalLinear.ord-tri`); Bedrock's `boundingOrd` supplies a *common"
  **Read, and the return's use is correct.** The archive records that
  `boundingOrd` was adopted to supply a COMMON stage. Common is not least,
  and the padding over the whole carrier is what a common bound permits and
  an exact rank forbids. The quote occurs at that line; I confirmed it.

## LITERATURE USED

- `dev/literature/devlin-II5.md:1`
  "# Devlin II.5: the Condensation Lemma and the GCH in L"
  Head read, then **declined**. II.5 is condensation and the GCH derivation.
  The three questions concern a recursion's value inside this tree's own
  code.
- `dev/literature/BIBLIOGRAPHY.md:1`
  "# Bibliography for the rud route"
  Head read, then **declined**. A bibliography index; no entry bears on the
  three questions.
- `dev/literature/digest.md:1`
  "# Digest: the orthodox form of the rud route, pinned from the collected literature"
  Head read, then **declined**. The rud route is a tower question. The
  divergence sits in `boundingOrd`'s index type and is route-neutral.
- `dev/literature/geology.md:1`
  "# Geology dossier: set-theoretic geology sources and the five questions"
  Head read, then **declined**. Grounds and mantles do not bear on the value
  of a well-founded recursion.
- `dev/literature/devlin-errata.md:1`
  "# Devlin errata: documented error classes (do-not-repeat checklist)"
  Head read, then **declined**. The errata list error classes in the Devlin
  text. The refuted term is this tree's own delivered code, not a
  transcription.
- Not a candidate; read to verify the return's literature claim:
  `dev/literature/truncation-and-selection.md:28`
  "`_build/literature/dev2.txt:1340-1350`. The least witness is the UNIQUE witness"
  **Read, and the return's use is sound.** The classical sources select the
  LEAST witness, and leastness is what makes selection definable. The same
  discipline separates a rank from a bounding ordinal. The quote occurs at
  that line; I confirmed it.
