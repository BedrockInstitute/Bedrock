# LJ-1.578: adversarial review of the LJ-1.578#1 return

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

The return under attack is `agents/tasks/LJ-1-578/lj-1.578-report.md`
with its stated NO-GO
`agents/tasks/LJ-1-578/review-of-cohyps-supplied.md`. The critic is not
the author of either file. I read the brief
`agents/tasks/LJ-1-578/LJ-1.578.md`, the probe
`agents/tasks/LJ-1-578/Probe578.agda`, the W3 slice
`agents/tasks/LJ-1-578/runs/W3.agda`, every transcript under
`agents/tasks/LJ-1-578/runs/`, and every `file:line` the return names.

## THE RECORD THE BRIEF NAMED, AND WHAT IT HOLDS

The brief told me to read `model`, `effort` and `heads_sha256` of the
LJ-1.578 instance in `dev/pod/transitions/`. This worktree's copy of
`dev/pod/transitions/2026-08.jsonl` has no line that names LJ-1.578.
The file ends before this instance. That is a gap in the worktree
record, not a defect in the return. The same facts exist in two other
places, and I used them.

- The facts block is at `agents/tasks/LJ-1-578/runs/accept-1.out:25`.
  It holds `exit_code 0`, `error_class null`, `heap_wall false`,
  `lines 0`, `obligations_delta 0`, `obligations_open 1`, `seconds 3.09`.
  Line 23 of the same file reads `# exit 0`. Line 20 reads
  `# obligations delta 0`. Line 16 reads `# run ... Probe578.agda rc 0
  seconds 3.58`. Line 17 reads `# run ... W3.agda rc 0 seconds 3.09`.
- The live record
  `/Users/alsg/Agentic/Bedrock/dev/pod/transitions/2026-08.jsonl`
  names this task. The coder ran as `model: "claude-opus-5"`,
  `effort: "xhigh"`, heads `d5caf66f` at dispatch (`:3189`) and at
  return (`:3215`, why `pid dead`). Acceptance held all six conjuncts,
  exit 0, `obligations_delta 0`, `obligations_open 1`, row
  `task-lj-1-578-stop-stated` (`:3221`). This critic runs as
  `model: "grok-4.6"`, `effort: "high"` (`:3223`). The critic is not
  the author. The invariant holds.

The facts that resolve agree with the return: exit 0, no error class,
obligations delta 0, one obligation still open. The dispatch to this
slot came from the `stop-stated` branch.

## QUESTION 1: DOES THE VERDICT LINE MATCH ITS OWN BODY?

**Yes.** The verdict line is at
`agents/tasks/LJ-1-578/lj-1.578-report.md:6`:
`verdict: NO-GO on `cohyps-supplied`; the remainder is ONE object with THREE clauses`.
The VERDICT section restates the same three claims
(`lj-1.578-report.md:18-35`). I checked each claim against the body,
against the stated NO-GO file, and against the tree.

1. `CoHyps` is not supplied. No term named `cohyps-supplied` is in
   `Probe578.agda`. The witness meter reports
   `1 UNRESOLVED of 1, 3.76 s, probe_red=False`
   (`agents/tasks/LJ-1-578/runs/witness-1.out:1-2`), with `[NotInScope]`
   on that name. Every term in the probe that mentions `CoHyps` is an
   implication with a named hypothesis:
   `three-give-cohyps` (`Probe578.agda:194-195`),
   `remainder-gives-cohyps` (`:462-463`),
   `certificate-gives-cohyps` (`:547-549`). None of `ThreeFacts`,
   `Remainder`, or `Certificate` is inhabited. The witness meter on
   those implications is `0 UNRESOLVED of 7`
   (`runs/witness-2.out:8`). An implication is not an inhabitant. The
   body does not read a discharge into them
   (`lj-1.578-report.md:270-274`, `review-of-cohyps-supplied.md:9-11`).
2. The remainder is one object with three clauses. `Certificate` is
   the product of `Cert.DefinesLevel`, `Cert.DefinesCover` and
   `BChain.DefinesLevelAcross` (`Probe578.agda:525-534`). The stated
   NO-GO names the same three clauses at the same lines
   (`review-of-cohyps-supplied.md:22-29`).
   `certificate-gives-cohyps : Certificate → P550.CoHyps` typechecks.
3. Row 3 is not paid. `CoHyps` is still a hypothesis of
   `gch-from-five` (`agents/tasks/LJ-1-564/Probe564.agda:456-461`).
   The bill still has five rows. The body says so
   (`lj-1.578-report.md:257-258`) and the stated NO-GO says so
   (`review-of-cohyps-supplied.md:52-54`).

The stated NO-GO file carries the same verdict with the same evidence.
Nothing in the body contradicts the line. This is not the LJ-1.373
defect class: the line, the body and the stated NO-GO file agree.

The brief caused this NO-GO by design, not by accident. It says
`DO NOT BUILD A LEVEL-HOOD CERTIFICATE. If that is what is left, name
it and stop` (`LJ-1.578.md:85-86`). The remainder is that certificate,
named as a type. A GO was not available without building it. The
brief did not hide a GO path.

## QUESTION 2: IS EVERY LOAD-BEARING CLAIM BACKED BY A file:line THAT RESOLVES TODAY?

I opened every load-bearing citation. They resolve, with one named
defect on the 176-line summary.

**The obligation and the stop.**
`LJ-1.578.md:11` and `:37` name `Probe578.agda::cohyps-supplied`.
`agents/tasks/LJ-1-550/Probe550.agda:215-230` is `CoHyps` at the
seventeen-slot frame. `src/L/BoundedSubset.lagda.md:1555-1558` is
`Co`'s two parameters. `Probe564.agda:456-461` is the five-row bill.
`Probe570.agda:110-116` is `row3-is-cohyps`. All resolve.

**The inventory this task built against.**
`agents/tasks/LJ-1-570/lj-1.570-report.md:46` is the `levelIn` heading
`NOT SUPPLIED, and not suppliable today`. `:78` is the same heading
for `cover`. `:58-61` is the down-reflection as the one term at the
site. `Probe570.agda:233-249` is `elem-down-at-the-site`.
`:62-64` names the hull's Skolem closure and the collapse iso as
machinery with no term at the site. `src/L/Hull.lagda.md:120` is
`closed`. `src/L/BoundedSubset.lagda.md:152` is `IsoInv`, `:195` is
`iso-inv`, `:321` is `CollapseIso`, `:350` instantiates it, `:1340`
is `hullExt`. `lj-1.570-report.md:96-98` is the three-item table
(`GraphAgree`, `HierInK`, hull re-basing).
`agents/tasks/LJ-1-532/Probe532.agda:274-277` is `HierInK`.
`Probe570.agda:289-294` is `GraphAgree`. `:319-322` is `Adeq`.
`:360-365` is `LevelInSuccOnly` and `strong-gives-weak`. All resolve.

**What this probe took, and what it paid.**
`Probe578.agda:44` is `import LJ-1-570.Probe570`. `:67-84` is
`CoverAt` with `w3-is-570s`. `Probe570.agda:84-96` is the source type.
`Probe578.agda:120-136` is the three facts (12 non-blank non-comment
lines). `:139-169` is `levelIn-from` and `cover-from` (27).
`:172-204` is `ThreeFacts` and the reductions (26). `:234-251` is
clauses (i) and (ii) (15). `:254-298` is `cert-gives-A` and
`cert-gives-C` (42). `:330-337` is `iso-inv-at-the-site` (6).
`:503-510` is clause (iii) (8). `:513-522` is `b-from-across` (10).
`:525-557` is `Certificate` and the reductions to the bill (28).
Each range matches the table at `lj-1.578-report.md:185-196`. The
table sums to 174. `src/V/Collapse.lagda.md:78` is `πX-member`,
`:86` is `πX-intro`, `:102` is `π∈-fwd`.
`src/L/BoundedSubset.lagda.md:1033-1034` is `condenses`.
`Probe578.agda:378-380` is `pair-gives-stage`. `:386-389` is
`StageGivesPair`, a type with no inhabitant. `Probe560.agda:165-176`
is `search-bounds`. All resolve.

**W3.** `lj-1.570-report.md:85-86` says `cover` asks for the same
adequacy as `levelIn` plus a least-witness selection.
`:88-90` says `cover` is general at every consumer.
`runs/W3.agda` is 60 physical lines and 32 non-blank non-comment.
`runs/w3-1.out:3-4` is exit 42 at the top-level module name.
`runs/w3-2.out:4` is `3.70 real`, exit 0. The brief estimated about
12 lines under 90 seconds (`LJ-1.578.md:109-110`). The number is 32
lines and 3.70 s.

**The 560 grep.** `ls agents/tasks/LJ-1-570/` returns four entries
and none is `LJ-1.570.md`. `review-of-cohyps.md:7` cites
`LJ-1.570.md:9-12`. The loose grep
`560|search-bounds|reflect` over that directory returns eight hits.
Six are the string `down-reflection`
(`Probe570.agda:136`; `lj-1.570-report.md:39`, `:59`, `:174`;
`review-of-cohyps.md:28`, `:46`). Two match on digits
(`lj-1.570-report.md:70` inside `:1560`; `runs/s1-2.out:24` inside
an instruction count). The strict grep
`LJ-1\.560|LJ-1-560|search-bounds|mkReflect|Single\.reflect|Reflect\.lagda`
returns zero. I re-ran both greps. They match the report.

**`LevelHood` has no consumer in `src/`.** `grep -n "LevelHood" src/`
returns three lines, all inside the two modules
(`src/L/BoundedSubset.lagda.md:74`, `:840`, `:844`). The in-fence
non-blank non-comment counts the report gives all match: `LevelHood`
`:74-147` is 65, `LevelHood0` `:840-869` is 19, `IsoInv` `:152-320`
is 158, `CollapseIso` `:321-355` is 22, `HullExt` `:1235-1345` is 91.

**Seconds.** Three forced rechecks, exit 0:
`runs/final-1.out:4` is 20.04 s at 2,493,874,176 bytes;
`runs/final-2.out:4` is 19.99 s at 2,493,857,792 bytes;
`runs/final-3.out:4` is 20.29 s at 2,493,857,792 bytes.
Median 20.04 s. Peak about 2.32 GiB against the 8 GB cap. No heap
event. `Probe578.agda` is 557 physical lines and 313 non-blank
non-comment. The section split 28+16+72+66+16+14+21+25+55 sums to
313. I re-counted the whole file. I removed the probe interface and
ran one Agda process under the pane caliber `GHCRTS=-A64m -I0 -M8g`.
Exit 0, 20.30 s, 2,493,906,944 bytes. The probe typechecks today.
Nothing is postulated. There is no hole.

**The 560 type argument.** `search-bounds` (`Probe560.agda:165-176`)
takes a formula and returns a stage. `LevelInH` and `CoverH`
(`Probe570.agda:154-163`) quantify over `HS.C.πX`. The term that
identifies that carrier with a stage is `condenses`
(`src/L/BoundedSubset.lagda.md:1033`), and it consumes the pair.
`pair-gives-stage` (`Probe578.agda:378-380`) is that consumption.
The circle is closed in Agda. The reflection step does not apply to
the pair.

**Literature the return used.** `dev/literature/devlin-II5.md:99`
is Devlin's (b). `:107-108` is the reverse inclusion. `:103-105` is
the collapse transfer plus 1.9.15. `archive/dev/DD-archived.md:37`
is DD27. `archive/dev/LJ-dispatch-index.md:198` is the 2.8k to 3.3k
price. `:222` is the 1.0k price. `archive/dev/JOURNAL.md:410` is the
codes-and-satisfaction sentence. All resolve as quoted.

**ONE DEFECT, NAMED.** The summary `176` does not mean what the
report says it means. The table at `lj-1.578-report.md:185-196` is
accurate: every range's non-blank non-comment count matches, and the
nine rows sum to 174. The remainder statements are 23 (15+8), and
that count matches. The line `everything paid ABOVE the remainder |
176 | the rest of the probe` (`:196`) does not follow from the
table. 23+176 is 199, which is neither 174 nor 313. 176 is the
complement of sections 3, 4 and 8 in the 313
(28+16+72+14+21+25). That cut throws out the paid terms in those
sections (`cert-gives-A`, `cert-gives-C`, `iso-inv-at-the-site`,
`b-from-across`) and keeps section 7, which names `Remainder`. It
is not "the rest of the probe" and it is not "everything paid above
the remainder". The next brief must not fund against 176. The paid
reduction is the table. The report already refuses 23 as a build
price (`:198-202`). That refusal stands. The NO-GO does not rest on
176: the obligation is uninhabited on the witness meter.

A smaller comment defect, not load-bearing: `Probe578.agda:57-59`
cites `lj-1.570-report.md:81-83` and `:86-88` for the hardness of
`cover`. The hardness marks sit at `:85-90`. The report itself cites
`:85-86` and `:88-90` (`lj-1.578-report.md:95-102`) and is right.

`AGENTS.md:45` is the analogy rule, as the report cites. It resolves.

## QUESTION 3: IS THE PREDECESSOR'S ENUMERATION COMPLETE?

**Yes.** I re-did the cure search at this site. I did not take it by
analogy.

No term of type `P550.CoHyps` is inhabited in this tree. Every
mention in a tracked probe is an implication
(`Probe570.agda:100`, `:188`; `Probe578.agda:194`, `:462`, `:547`;
and the bill hypotheses in `Probe564.agda`, `Probe569.agda`,
`Probe571.agda`). There is no hidden inhabitant.

`LevelHood` is syntax without a theorem. Its three `src/` hits are
self-references. Consuming it at `DefinesLevel` would require a
formula over `T.Code` together with uniqueness of the witness. That
is the certificate the brief forbids (`LJ-1.578.md:85-86`). It is
not a cheap glue term of the `iso-inv-at-the-site` kind.

`[LJ-1.570]`'s three missing items (`GraphAgree`, `HierInK`, hull
re-basing, `lj-1.570-report.md:92-98`) are the assembly of that
certificate, not a second path around it. This return listed those
marks, then cut a different remainder: `Certificate`, with a
typechecked implication to `CoHyps`. That is a sharpening of the
inventory, not a miss. The brief forbade building the certificate,
so it forbade pushing those three items.

`search-bounds` does not apply to the pair, for a reason that is a
type (`Probe560.agda:165-176` against `Probe570.agda:154-163`).
Reflection would act inside clause (i), which is the certificate.
`StageGivesPair` (`Probe578.agda:386-389`) is named and uninhabited.
The return does not claim it.

W3 named `cover` and specified the type. The coder wrote the slice
and typechecked it alone. A21 asks whether the mathematician named
the term and the probe, and never whether it wrote one. This return
is a coder return. The name and the slice are present.

W7 holds of the remainder: clauses (i) and (ii) are over `T.Code`
(`Probe578.agda:237`, `:247`), not over `Formula CS.S 4`. DD27 is
the warrant (`archive/dev/DD-archived.md:37`).

W8 does not abort this return. The task was a build, not a
provability question. The return says it read the literature after
the split typechecked (`lj-1.578-report.md:141-143`). That is a
check, not a design input. No erratum in
`dev/literature/devlin-errata.md` touches II.5: the documented
problems are Chapter I section 9 and Chapter VI section 1
(`devlin-errata.md:40-41`).

Two precision notes for the next brief, neither of which weakens
the NO-GO.

1. `Certificate` is a product of three independent formula-existence
   statements. `DefinesLevel` and `DefinesCover` quantify over
   `Formula T.Code 1` (`Probe578.agda:237`, `:247`).
   `DefinesLevelAcross` quantifies over `Formula CI.I.SM 1`
   (`:508`). The three clauses do not share one `φ`. A brief that
   says clauses (ii) and (iii) reuse clause (i)'s formula
   (`lj-1.578-report.md:299-301`) must fund the translation between
   those signatures. The product type still implies `CoHyps`.
2. Facts A and C spend the hull's Skolem closure
   (`Probe578.agda:259`, `:282`, via `T.closed` at
   `src/L/Hull.lagda.md:120`). The inventory mark "machinery, no
   term at the site" therefore moved for Skolem as well as for the
   collapse iso. The return named only the iso as moved
   (`lj-1.578-report.md:54-61`). The Skolem spend is in the file. It
   is not hidden.

The return did not price the proof of any clause of `Certificate`.
It says so (`lj-1.578-report.md:198-202`). That is the honest
remainder: a named type, not a guessed line count. A brief funded
against 23 would be funded against the wrong number.

## VERDICT

**Upheld.** The verdict is correct on its own obligation numbers:
`cohyps-supplied` is out of scope, `probe_red` is false, one
obligation remains open. The measurement of the table, of the 23
statement lines, of the 313-line file, of the times, and of the
witness meter is sound. The 176-line summary is a real cut of the
file and a wrong label; it does not carry the NO-GO. The brief
caused the stop by its own abort on a level-hood certificate, and
that is what remains. No cure in the tree today was missed. An
upheld NO-GO closes the task.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: read at `:410`. Quote:
  `level-hood must run through codes and satisfaction, and those leaves are`.
  Used to check the predecessor's citation. The quote sits at that
  line. It does not change the NO-GO.
- `archive/dev/ORCHESTRATION.md`: read at `:1`. Quote:
  `# ORCHESTRATION: the orchestrator's operating rules`.
  Declined, not used. Retired orchestrator rules. This review judged
  one return against one brief.
- `archive/dev/DD-archived.md`: read at `:35`. Quote:
  `The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed.`.
  Used. Those four are the lens of this review. Also opened `:37`.
  Quote at `:37`:
  `THE HULL IS INDEXED BY A META TERM ALGEBRA, not by object-language formulas.`.
  Used to check that clauses (i) and (ii) sit on `T.Code`.
- `archive/dev/PLAN-archived.md`: read at `:1`. Quote:
  `# ARCHIVED 2026-08-20`.
  Declined, not used. Retired plan. The queue is the producer.
- `dev/ARCHIVE.md`: read at `:1`. Quote:
  `# ARCHIVE.md: the archive registry`.
  Declined, not used. No module was retired by this task. W4 did not
  fire.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:99`. Quote:
  `> (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)].`.
  Used. I confirmed the predecessor's identification of clause (i)
  with Devlin's (b), of clause (ii) with the reverse inclusion at
  `:107-108`, and of clause (iii) with the transfer at `:103-105`.
  The identification is a check. It does not inhabit `Certificate`.
  W8 does not block the shape: II.5 is a theorem with conditions
  this tree is already aiming at, not an axiom with no condition
  this tree meets.
- `dev/literature/BIBLIOGRAPHY.md`: read at `:1`. Quote:
  `# Bibliography for the rud route`.
  Declined, not used. No new source was consulted.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. `devlin-II5.md:18-20` already records that the
  digest's II.5 entry carries no part of the chain.
- `dev/literature/geology.md`: read at `:1`. Quote:
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  Declined, not used. Geology does not bear on the certificate or on
  the pair.
- `dev/literature/devlin-errata.md`: read at `:41`. Quote:
  `section 9 of Chapter I and section 1 of Chapter VI.`.
  Used. No erratum applies to II.5. W8 has no literature NO-GO here.

## WHAT I DID NOT DO

- I wrote no file but this one. I did not commit. I did not push.
- I did not edit `src/`, the probe, the report, the stated NO-GO, or
  the runs.
- I removed the probe interface and ran one Agda process to check
  the probe is green today. The regenerated interface file sits
  under `_build/`, which git ignores. The tracked working tree is
  unchanged except for this review file.
