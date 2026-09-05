# LJ-1.391: adversarial review of the LJ-1.391#1 return

slot: `mathematician_adversarial`. Attacked return:
`agents/tasks/LJ-1-391/lj-1.391-report.md`, instance `glm-5.3`, effort `""`,
`heads_sha256 1b0bc651`, role `coder`, acceptance record
`dev/pod/transitions/2026-08.jsonl:73` (the record whose `"seq"` is 74) and
`agents/tasks/LJ-1-391/runs/accept-1.out`. Evidence is `file:line` throughout,
and every quote below was read at the line it is cited at, on 2026-08-19.

## THE OUTCOME OF THIS REVIEW

**THE NO-GO VERDICT STANDS. A review that agrees is a real result, and this
one agrees after re-measuring.** The probe is RED at exactly one hole under my
own runs, the green half is green, and my own sweep supports the route B
conclusion.

**BUT THE ENUMERATION IS NOT COMPLETE, AND FOUR EVIDENCE DEFECTS STAND.** The
return's route table names two routes, closes one of them with a grep sentence
that is false as written, and skips the two checklist steps that the digest and
the tree's own measured law C-54 order FIRST at this exact stall shape. Three
orders the work brief gave are dropped. One generality sentence in the body
claims more sites than were measured.

## WHAT I RE-MEASURED

| Check | Command and result | Outcome |
|---|---|---|
| full file, 3 runs | `agda --safe agents/tasks/LJ-1-391/Probe391.agda` under `GHCRTS=-A64m -I0 -M8g` | rc 42 each run, 1.57, 1.58, 1.62 s. The ONLY error is `[UnsolvedInteractionMetas]` at `Probe391.agda:149.35-59`. Confirms "RED at exactly one hole, nothing else" |
| floor, 3 runs | the file replaced in place by its first 48 lines, then restored | rc 0 each run, 1.54, 1.53, 1.54 s. Restored byte-identical: `cmp` silent, sha256 `ff3fa7e9...` before and after. Confirms the floor claim and the 0.04 s delta over floor |
| program witness | `agents/tasks/LJ-1-391/runs/accept-1.out:20` `# wall seconds 1.51`, `:22` `# exit 42`, `:24` `"error_names_all": ["UnsolvedInteractionMetas"]` | agrees with the return: the full file runs at its floor, Parts 1 and 2 contribute no error |
| code lines | non-blank, non-comment lines, the return's own definition | `:64-74` has 10, `:89-91` has 3, `:96-101` has 6, `:108-110` has 3, `:145-149` has 5. Sum 27, obligations 10 + 5 = 15. The return's table says 11, 2, 4, 3, 5, sum 25, obligations 16. The whole-file count, 149 lines and 50 code lines, is exact |
| SWO sweep | `grep -rn ": SWO\|SWO (" src/` | returns 20 more shapes than the return names. See QUESTION 3, GAP 2 |
| gates | `lint-agda.py`, `check-glossary.py`, `check-fences.py`, `check-probes.py`, `lint-prose.py` run by me, all rc 0; `check-unbound-hyp.py --check` names the same five hypotheses at the same five lines the return lists | the return's gate claims reproduce |
| dropped terms | `grep -n -i "axiom\|3.8.1\|hott\|admissib\|branch\|2-Constant\|rec→Set\|Kraus\|constant"` over the return | zero lines. See QUESTION 3, GAP 1 and GAP 3 |

My run times sit above the return's 1.56 s and the program's 1.51 s because
this machine is loaded now. All three measurements agree on what matters: the
full file costs its floor, so "instantiating the chapter is free" holds, and
the 0.04 s delta is inside the floor's own recorded spread, 1.49 to 1.56.

## QUESTION 1: does the verdict line match its own body?

**YES.** The verdict line claims three things and the body delivers each:

1. **`sq-collect-suffices` is GREEN.** The body's evidence is a control run
   that was discarded, so it leaves no artifact. The claim resolves today two
   ways: my full-file runs report the one meta at `:149` and nothing else, so
   Parts 1 and 2 are green inside the surviving file, and the acceptance
   record agrees (`runs/accept-1.out:24`).
2. **`sq-collect` is RED at exactly one hole.** Verified by my own three runs:
   rc 42, sole error at `Probe391.agda:149.35-59`, the span of the hole
   `{!  PointwiseUntrunc  !}` on line 149.
3. **The door is load-bearing.** The body's chain is: the consumer takes the
   family as an untruncated module parameter (`src/L/StageCardinal.lagda.md:15`
   to `:19`, and `sq` is applied at exactly one place, `:283` `module B = Bound
   α oα infα (sq α α∈suc infα)`, confirmed by my own grep), the collection is
   the only bridge from the truncated supply, and the collection reduces to
   `PointwiseUntrunc` by a green term (`Probe391.agda:96-101`) with the hole at
   `:149`. I also measured the leg the return left unchecked, the [T46]
   reading, and it HOLDS. See QUESTION 3, GAP 3. It strengthens this verdict.

Two sentences of the verdict block are weaker than the verdict itself:

- **"This tree carries none", a selection on the ambient pairing type.** The
  body supports it with the route table, and route B's row closes with a grep
  sentence that is false as written (QUESTION 2, D2). I re-ran the sweep and
  the conclusion survives it. The defect is in the evidence sentence, not in
  the verdict.
- **"No device in the tree today selects an ambient pairing, at any band,
  under any caliber"** (section 2). This sentence claims more than the body
  measured. The probe measures ONE site, the generic parameter `α₀`. Law C-42
  says a refutation measures the site it names and never how far that site
  extends, and no second site was run. At the one concrete band this tree can
  already read, `α₀ = ω`, the band collapses to the singleton `{ω}`, the
  supply is already data (`squareω : sq ω`, `src/L/InjChain.lagda.md:184`), and
  the chapter itself passes `ω` as a band member
  (`src/L/StageCardinal.lagda.md:550`, the call `IH ω ... (∈-irrefl ω)`), so no
  selection is needed there at all. The same section's closing sentence, "AT
  GENERIC `α₀`", is the correct scope, and the verdict for the campaign's deep
  sites survives. The overreach is in the sentence, not in the verdict.

## QUESTION 2: is every load-bearing claim backed by a file:line that resolves today?

**ALL BUT FOUR.** The four defects, worst first:

- **D1, a mis-citation.** The return quotes the flip refutation under
  `dev/literature/truncation-and-selection.md:311-314`, in the verdict table
  and again in its LITERATURE USED block. The quoted text, "It is then REFUTED
  because it is SYMMETRIC ... The whole refutation is the flip of a pair and it
  uses no excluded middle", sits at `:307-310`: line 307 ends "It is then",
  line 308 is "REFUTED because it is SYMMETRIC, so it is injective only if the
  carrier is a", and the sentence closes at `:310`. Line 311 is blank, and
  `:312` opens a DIFFERENT passage, the family refutation. A checker opening
  `:311-314` does not find the quote. Correct citation: `:307-310`. The probe's
  own comment carries a cousin of this error, `:311-318` at
  `Probe391.agda:117`, but that span does contain the family refutation at
  `:312-316`, so it resolves.
- **D2, a false evidence sentence.** "a `grep -rn ": SWO\|SWO (" src/` returns
  no other shape" is false today. My run of that exact grep returns, among
  others, `lex2 : SWO (⟪ α ⟫ × ⟪ α ⟫)` (`src/L/Ordinal/SquareLaw.lagda.md:282`),
  `lex3` (`:285`), `godSWO : SWO Pair` (`:308`), `god : SWO PairA` (`:755`),
  `natOrder : SWO {ℓ-zero} ℕ` (`src/L/Choice/Finite.lagda.md:596`), `order :
  SWO (Point n)` (`:884`), `limitOrder : SWO Limit` (`:1114`), `nameOrder :
  SWO (Name)` (`src/L/Choice/Name.lagda.md:804`), `stepOrder` (`src/L/Choice/
  Faithful.lagda.md:400`), `ordW : SWO ⟪ Lset δ ⟫` (`src/L/Choice/Order.lagda.md:222`),
  `wL : SWO SL` (`src/L/Hull.lagda.md:158`) and `pullOrder : SWO B`
  (`src/L/Choice/Step.lagda.md:242`). Three of the misses sit in the very file
  the route B row cites. The CONCLUSION survives my sweep: no delivered SWO in
  the tree has an ambient function type as its carrier. The sentence as
  written is not evidence.
- **D3, a range one line short.** The sentence "A canonical injection needs a
  well-order on the INJECTIONS ..." begins on
  `dev/literature/truncation-and-selection.md:335` and its last word "have"
  sits at `:337`. The cited range `:334-336` cuts the final line and includes
  the wrong lead-in at `:334`. Correct span: `:335-337`. The work brief
  injected the shorter span, so the return inherited it, and inheritance is
  not a correction.
- **D4, arithmetic.** The per-term code-line counts, 11, 2, 4, 3, 5, sum 25,
  and "16 code lines for the two obligations", do not match the file under the
  return's own definition of a code line. Measured: 10, 3, 6, 3, 5, sum 27,
  obligations 15. The whole-file count, 149 lines and 50 code lines, is exact.

Everything else I checked resolves, and I checked all of it:
`Probe391.agda:64-74`, `:70-74`, `:89-91`, `:96-101`, `:108-110`, `:112-118`,
`:145-149`, `:149.35-59`; `src/L/Ordinal/SquareLaw.lagda.md:127`, `:176`,
`:685-687`, `:963-964`; `src/L/StageCardinal.lagda.md:15-20`, `:283`,
`:419-420`, `:530-533`, `:564-566`; `src/L/WellOrder/Base.lagda.md:158-160`;
`agents/tasks/LJ-1-314/CodeUntrunc.agda:57-66`; `src/L/Choice/Step.lagda.md:730`;
`src/L/GCH.lagda.md:37-38` and `:59-66`; `src/L/InjChain.lagda.md:184-185`;
`agents/tasks/LJ-1-388/lj-1.388-report.md:236-248`;
`agents/tasks/LJ-1-390/lj-1.390-report.md:20-27`; and every archive row of the
return, re-read at the cited lines for this review's ARCHIVE USED block.

## QUESTION 3: is the enumeration complete?

**NO. FOUR GAPS.** The first is the material one.

**GAP 1, THE DIGEST'S OWN CHECKLIST AND THE TREE'S OWN LAW C-54 BOTH ORDER A
QUESTION THE RETURN NEVER ASKS.** `dev/literature/truncation-and-selection.md:287`
opens: "When a proof in this tree stalls on `∥ A ∥₁`, ask in this order." The
steps at `:289-302` are: (1) goal a proposition, (2) `A` a proposition, (3)
goal a SET plus a `2-Constant` map `A → goal`, so `rec→Set` applies, (4) `A`
decomposes over a well-order with propositional payload, so `leastOf` applies,
(5) a weakly constant endomap by any other route, necessary and sufficient by
Kraus et al., Theorem 16. A sixth step is added at `:324`: only then is a new
principle in question. The return's route A is steps 1 and 2. The return's
route B is step 4. **Steps 3 and 5 are named nowhere: my grep for "2-Constant",
"rec→Set", "Kraus" and "constant" over the report and the probe returns zero
lines.** This is not a literature nicety. It is a measured law of this tree,
C-54, `dev/LESSONS.md:4448`: "A truncation stall at a SET motive is a
`2-Constant` obligation before it is a principle", and its rule at `:4455-4456`
is "motive the obligation is exactly a `2-Constant` map, and a stall is a term
you / have not written rather than an axiom the theory lacks." The digest's
practical rule says the same, `:193-196`: "It is a `2-Constant` proof.
Discharge it or refute it before pricing anything else."

The stall here is exactly that shape. `sq δ` is a Σ whose first component is a
function space (`src/L/Ordinal/SquareLaw.lagda.md:686`), a set and not a
proposition, so route A dies at `isProp (sq δ)` and the digest's step 3 applies
to the same motive. By the equivalence the digest records at
`trunc→Set≃` (`:186`, stated at `:189-190` as "For a set `B`, the maps out of /
`∥ A ∥₁` ARE the weakly constant maps `A → B`"), the per-`δ` component of
`PointwiseUntrunc` (`Probe391.agda:89-91`), which is `∥ sq δ ∥₁ → sq δ`, is
EQUIVALENT to a `2-Constant` endomap of `sq δ`, given `sq δ` is a set. So the
sharpened reading of this gap is:

- It is NOT a free cure. By the digest's own necessity, paying the endomap IS
  paying the residue, so the NO-GO does not fall by the gap alone.
- It IS an unmeasured upgrade. The flip refutation closes `isProp (sq δ)` and
  nothing else: a `2-Constant` endomap may send the pairing and its flip to
  the same element, and the digest's family refutation at `:312-313`, "Every
  canonical / pairing that reads only the reachable set is symmetric, hence
  not injective", refutes readers, that is candidate elements, and not
  endomaps. The digest itself lists the endomap question as open, `:330-331`:
  "Whether a given payload has a weakly constant endomap. That is a per-site /
  question and this file gives only the criterion." A refutation of the
  endomap at ONE band member would upgrade the NO-GO from a device survey to
  an unprovability theorem, and the digest orders that question FIRST.
- **THE CURE IS ONE PROBE, and W3 as amended by A21 fixes who writes it: this
  review names it, and the coder writes it.** State the `2-Constant` endomap
  obligation for `sq δ` at generic `α₀`, with the sethood of `sq δ` as its
  first conjunct, and either discharge it or refute it. A discharge collapses
  the NO-GO. A refutation is the strongest result available to this campaign
  on this door.

Part of this gap traces to the BRIEF, and my slot must say so. The brief's
REASONING framed the honest question as "does this tree's selection device
reach an ambient pairing function", which is step 4 alone, and its injected
law list carried C-42 but not C-54. The return adopted the frame, extended it
by one route, and closed it with a false sentence of its own. So: the frame is
the brief's, the false closure is the return's, and the omission is shared.

**GAP 2, THE SWO INVENTORY.** The return names `ordSWO`, `orderAt` and
`prodSWO`, and closes the row with the false grep sentence (D2). It also
misses the tree's one generic well-order TRANSFER device: `pullOrder`
(`src/L/Choice/Step.lagda.md:226-242`), which builds `SWO B` from an injection
`f : B → C` into any well-ordered `C` (`:227` "(f : B → C) (finj : (u v : B) →
f u ≡ f v → u ≡ v) where", `:242` "pullOrder : SWO B"). It does not rescue
route B: with `B` the ambient function type, the injection into a coded
carrier IS the door `[LJ-1.386]` measured. But an enumeration that misses the
transfer device and asserts a false grep to close itself is not complete. After
my sweep of every shape the grep returns, the route B conclusion stands: no
delivered SWO in the tree has an ambient function type as carrier.

**GAP 3, THREE ORDERS THE BRIEF GAVE AND THE RETURN DROPPED.** My grep over
the return for each topic returns zero lines.

- **The [T46] check.** The brief ordered: read `branch` at
  `src/L/StageCardinal.lagda.md:534-560` and say whether the elimination of
  the induction hypothesis lands in the empty type or in an injection. I ran
  it. The hypothesis is consumed at `:550-551`, "comp-inj (IH ω (subst (λ w →
  ⟨ w ∈ˢ α ⟩) e δ∈α) ω-ord ω∈suc (∈-irrefl ω))", and at `:556`, "comp-inj (IH
  δ δ∈α oδ δ∈suc infδ) (Emb.emb α oα δ δ∈α)", and both land in the injection
  type `⟪ Lset δ ⟫ ↪ ⟪ α ⟫`. The only `Empty.rec` in sight, at `:528`,
  eliminates the false membership case, not the hypothesis. **The brief's
  reading is right: this chapter is a [T46] site. The truncated grade fails
  inside the chapter as well, so `sq-collect` is not the only thing that
  fails, and the T47 dodge of restating the parameter as truncated is not free
  here.** This STRENGTHENS the verdict. The return reached the right verdict
  with this leg unchecked, and an unchecked leg that happens to hold is still
  an omission.
- **The admissibility remark.** The brief ordered: say whether a choice
  principle stated the same way would now be admissible, given that `lem` is
  one (`src/L/StageCardinal.lagda.md:15`), and do not decide it, because the
  archived objection has moved. The return quotes the old objection,
  `archive/dev/JOURNAL-archived.md:1630` "a choice principle implies excluded
  middle and would cost the tree's postulate-free claim", and stops there. It
  never says whether the parameter form would be admissible. The standing
  ruling it would quote is D2, `archive/dev/DECISIONS-archived.md:30`: "LEM
  (and any classical/choice principle) is an explicit parameter; the whole
  tree is `--safe`."
- **The digest's name for the principle.** The brief ordered, in capital
  letters: "`sq-collect` IS THE AXIOM OF CHOICE AND THE DIGEST SAYS SO. DO NOT
  PRESENT IT AS A NEW STATEMENT", and "name the principle as the digest names
  it". The digest names it at `:223-227`: section "The axiom of choice does
  NOT give an untruncated selection", HoTT Book 3.8.1, with the form
  "(∏x ∥Y x∥) → ∥∏x Y x∥" at `:227`. The return coins "PointwiseUntrunc" and
  says "the choice principle" twice, and the strings "axiom of choice",
  "3.8.1" and "HoTT" appear nowhere in it. The residue is honestly stated as
  a type and never postulated, so DD9 is respected, but the ordered
  identification is absent, and a reader of the return alone cannot tell that
  the missing principle is the one the digest already catalogued.

**GAP 4, THE SCOPE SENTENCE.** Section 2's "at any band, under any caliber"
is the defect already given under QUESTION 1: one site was measured, the
generic parameter; C-42 forbids extending a refutation past the site it names;
and the one concrete band the tree can read, `ω`, has the supply as data
(`src/L/InjChain.lagda.md:184`) and needs no selection. "Under any caliber" is
likewise unmeasured: one caliber was run. Provability does not vary with
caliber, so the phrase is either vacuous or unmeasured, and a report should
not carry either.

## THE SIX FACTS OF THE INSTANCE

From `dev/pod/transitions/2026-08.jsonl:73` (acceptance, `"seq"` 74) and
`agents/tasks/LJ-1-391/runs/accept-1.out`:

| Fact | Value | The return says |
|---|---|---|
| exit_code | 42 | "exit 42" |
| error_class | `unsolved_meta` | "`[UnsolvedInteractionMetas]`" |
| heap_wall | false | "no heap event appeared" |
| seconds | 1.51 | median 1.56 of its own three runs; both at the floor |
| changed_files | `Probe391.agda`, `lj-1.391-report.md` | "I changed two files and both are mine" |
| obligations_delta | 0 | one obligation green, one red by design, none closed |

All six are consistent with the return's body, and the instance header is
`model glm-5.3`, `effort ""`, `heads_sha256 1b0bc651`. The branch that fired
was `task-lj-1-391-no-go-attacked`, the escalation this review answers.

## WHAT THIS REVIEW CHANGES

1. **Anyone who cites the return must not cite its grep sentence or its
   `:311-314` citation.** Use the corrected spans, `:307-310` for the flip and
   `:335-337` for the well-order prediction, and my sweep in place of "no
   other shape". Use 15, not 16, for the two obligations' code lines.
2. **The next measurement is named: the `2-Constant` endomap of `sq δ`, at
   generic `α₀`, with the sethood of `sq δ` as the first conjunct.** Discharge
   or refute, per the digest's order at `:193-196` and law C-54. A refutation
   upgrades the NO-GO to an unprovability theorem and keeps the door
   `[LJ-1.386]` on the critical path with one more leg measured. A discharge
   collapses the NO-GO. Either result closes the question this task opened.
3. **The [T46] reading is now measured**, in this file, QUESTION 3, GAP 3,
   and it supports the verdict: the chapter cannot be re-pointed at a
   truncated parameter for free.
4. **No standing price changes.** Both route residues keep their recorded
   costs, as the return states. The scope sentence "at any band" should be
   read as "at the generic band of the campaign's sites".

## WHAT THIS REVIEW DID TO THE TREE

I wrote this file and nothing else. The floor control replaced
`agents/tasks/LJ-1-391/Probe391.agda` in place by its first 48 lines for three
runs and then restored it: `cmp` is silent and the sha256 is `ff3fa7e9...`
before and after, the same digest the file carried when I arrived. My run
outputs sit in `/tmp`, outside the tree. I ran no `git add`, no commit and no
push.

## ARCHIVE USED

| Injected path | Read | What it gave |
|---|---|---|
| `archive/dev/JOURNAL-archived.md` | `:1626`, `:1630`, `:1697`, `:1700`, `:1724` | the [T43], [T46] and [T47] records the return leans on; every quote resolves at those lines |
| `archive/dev/DECISIONS-archived.md` | `:30` | D2, the ruling the dropped admissibility remark would have quoted |
| `archive/dev/TASKS-archived.md` | `:82` | T47's row, DELIVERED, as the return cites it |
| `dev/ARCHIVE.md` | `:1` | DECLINED, `not used`. Line 1 is "# ARCHIVE.md: the archive registry". A registry index; its rows point at the files quoted above and add nothing |
| `archive/src/2026-08-09-rud-route/L/Coding/Environment.lagda.md` | `:1` | DECLINED, `not surveyed` beyond the head. Line 1 is "# Environments as sets", the retired route's environment module. Nothing in a retired environment module bears on a collection step at the live chapter |

`archive/dev/JOURNAL-archived.md:1626`:

> counting's bounds in TRUNCATED form, since every consumer goal in the chain is a proposition and

`archive/dev/JOURNAL-archived.md:1630`:

> evidence: a choice principle implies excluded middle and would cost the tree's postulate-free claim,

`archive/dev/JOURNAL-archived.md:1697`:

> NOT proposition-valued: its first component is a function, so a truncated equinumerosity cannot

`archive/dev/JOURNAL-archived.md:1724`:

> and it is FALSE as priced**: to CONSUME the truncated hypothesis one must still PROVIDE it at every

`archive/dev/DECISIONS-archived.md:30`:

> LEM (and any classical/choice principle) is an explicit parameter; the whole tree is `--safe`.

`archive/dev/TASKS-archived.md:82`:

> | L3.32-T47 | Truncated square law at initial ordinals | DELIVERED | `_build/l3.32-t47-report.md` |

## LITERATURE USED

| Injected path | Read | What it gave |
|---|---|---|
| `dev/literature/devlin-II5.md` | `:63` | DECLINED for mathematics, `not used` beyond the check. My grep for truncat, collect, choice over it returns one line, `:63` "choice. 5.1 is proved in the chapter, not assumed. Its role in the spine is", which is the condensation spine and not the collection step. The return's decline of this file is honest |
| `dev/literature/BIBLIOGRAPHY.md` | `:1` | DECLINED, `not used`. Line 1 is "# Bibliography for the rud route". A source list for the retired route; nothing on truncation |
| `dev/literature/digest.md` | `:1` | DECLINED, `not used`. Line 1 is "# Digest: the orthodox form of the rud route, pinned from the collected literature". The retired route's digest; the live digest for this question is `truncation-and-selection.md` |
| `dev/literature/geology.md` | `:1` | DECLINED, `not used`. Line 1 is "# Geology dossier: set-theoretic geology sources and the five questions". Set-theoretic geology; no bearing on a collection step in `L` |
| `dev/literature/devlin-errata.md` | `:1` | DECLINED, `not used`. Line 1 is "# Devlin errata: documented error classes (do-not-repeat checklist)". A do-not-repeat checklist for Devlin readings; this review reads no Devlin proof |

Also used, and it is the load-bearing literature for this review:
`dev/literature/truncation-and-selection.md`, at `:174-176` (`rec→Set`),
`:186` and `:189-190` (`trunc→Set≃`), `:193-196` (the 2-Constant rule),
`:223-227` (AC, HoTT Book 3.8.1, the digest's name for the principle), `:287`
and `:289-302` (the checklist), `:307-310` (the flip refutation, corrected
span), `:312-313` (the family refutation), `:324-326` (the added sixth step),
`:330-331` (the endomap question left open), `:335-337` (the well-order
prediction, corrected span). It is not in my injected candidate list, and I
name it so the list above stays complete.
