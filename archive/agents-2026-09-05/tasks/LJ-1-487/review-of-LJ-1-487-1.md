# LJ-1.487 adversarial review of LJ-1.487#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld

The return under attack is `agents/tasks/LJ-1-487/lj-1.487-report.md`
(coder LJ-1.487#1, model `grok-4.6`, effort `high`, heads_sha256
`5f213519`, per `dev/pod/transitions/2026-08.jsonl` seq 1671/1726),
with its stated NO-GO in
`agents/tasks/LJ-1-487/review-of-CoverWitnessesInHull.md`. The
acceptance facts of that instance: exit_code 0, obligations_delta 0,
obligations_open 1, heap_wall false, error_class null
(`agents/tasks/LJ-1-487/runs/accept-1.out`, conjuncts 1-6 all true).

## QUESTION 1. DOES THE VERDICT LINE MATCH THE BODY?

**Yes.** The verdict line
(`agents/tasks/LJ-1-487/lj-1.487-report.md:172-176`) states four
things and the body delivers each:

1. **"W3 is GO: `wit` names an ordinal at `isOrdFo`."** The term
   `ord-by-wit` is inhabited at `agents/tasks/LJ-1-487/Probe487.agda:122-128`,
   and it is inside every kept full-file check. Three forced W3-only
   rechecks, each exit 0, each with one `Checking` line
   (`runs/w3-1.out`, `runs/w3-2.out`, `runs/w3-3.out`).
2. **"The covering formula packages and feeds to `wit`.**" `coverIndex`
   (`Probe487.agda:139-143`), `packagedCover` (`:145-146`) and
   `feed-cover` (`:153-154`) typecheck inside the exit-0 full runs
   (`runs/full-recheck-{1,2,3}.out`).
3. **"The obligation term is not written."** `CoverWitnessesInHull`
   is a `Type` at `Probe487.agda:163-166` and no term of it exists in
   the file. The body says the same at `lj-1.487-report.md:290-294`.
4. **"Witness meter: 1 UNRESOLVED of 1, `probe_red=False`
   (`runs/witness.out:1-2`)."** The file's second line reads
   `witness: 1 UNRESOLVED of 1, 2.80 s, probe_red=False`. It resolves.

The stated NO-GO file says the same as the report body: NO-GO at the
covering index in `M`, W3 GO, no term, no refutation
(`review-of-CoverWitnessesInHull.md:26-45`). No line in the return
contradicts another line. The 2026-08-16 defect class (verdict line
unread against the body) is absent here.

## QUESTION 2. DOES EVERY LOAD-BEARING `file:line` RESOLVE TODAY?

**Yes.** I opened every load-bearing citation. All resolve, and each
says what the report says it says.

In `agents/tasks/LJ-1-487/Probe487.agda`: `:52-55` `isOrdFo`, `:61-64`
`HullStage`, `:79-80` the `⊥*` instantiation, `:85-91` `sat-empty`,
`:102-117` `isOrdFo-out`, `:122-128` `ord-by-wit`, `:139-143`
`coverIndex`, `:145-146` `packagedCover`, `:153-154` `feed-cover`,
`:163-166` the obligation type. All exact. Total lines 167 and
non-blank non-comment lines 93, as claimed.

In `src/L/Hull.lagda.md`: `:72-74` `Code` is `base` or `wit`; `:74`
`wit` takes `Formula (⊥* {ℓ}) (suc k)`; `:120-123` `closed`, the
definable-existence closure; `:153` `AbsL`; `:174-176` the
`Elementary` type at `Formula SM`; `:323` the term algebra at
`AbsL.𝒮M`; `:337-339` `hull-member`. All exact.

In `src/L/BoundedSubset.lagda.md`: `:795-798` `isOrdAt`, same spelling
as `isOrdFo`; `:759-760` `elem : A.Elementary`, inside
`HullElemDown`...`WithCode` (module at `:667` and its `WithCode`
submodule, four-space indent at `:759`); `:903-914` the `HullStage`
telescope, which `Probe487.agda:61-64` copies faithfully; `:1543-1545`
the consumer at the concrete `UK.X`. One cosmetic defect: the report
cites `reverse` at `:865-69` but the name and the type ascription
`reverse : Formula CS.S 1` sit at `:864-865`; the cited range still
resolves and carries the definition body. Not load-bearing.

Elsewhere: `src/L/Coding/Sequence.lagda.md:349` exposes
`LsetGraphAt`; `src/FOL/Manipulation/Parameters.lagda.md:260` is
`absFo`; `src/L/Hierarchy.lagda.md:334-335` `Lset-only` and `:646-648`
`Lset-defines`; `dev/literature/devlin-II5.md:95`, `:107`, `:108`
match the report's quotes character for character; `dev/pod/direction.md:37`
is the standing direction as quoted;
`agents/tasks/LJ-1-484/lj-1.484-report.md:114` is the `## VERDICT`
heading and `:116-121` matches the report's quote verbatim; `:129-185`
is `## THE DECOMPOSITION` as quoted;
`agents/tasks/LJ-1-484/Probe484.agda:68-69`, `:80-82`, `:88-98`,
`:110-112`, `:123-126` all hold the named terms and types, and
`:123-126` is character for character the type restated at
`Probe487.agda:163-166`; `agents/tasks/LJ-1-462/lj-1.462-report.md:77`
is NO-GO at D-10 step 3; `agents/tasks/LJ-1-472/lj-1.472-report.md:151`
is that report's `## VERDICT` (GO, numerals);
`agents/tasks/LJ-1-474/lj-1-474-report.md:70` likewise (GO, codes);
`agents/tasks/LJ-1-160/lj-1.160-report.md:248` carries the
non-transitivity measurement.

The runs. Every number in the two recheck tables matches its kept
`.time` file to the byte: `w3-1` 2.49 s / 477478912, `w3-2` 2.24 s /
477478912, `w3-3` 3.78 s / 396771328, medians 2.49 s and 477478912;
`full-recheck-1` 4.37 s / 1105379328, `full-recheck-2` 4.39 s /
1105379328, `full-recheck-3` 4.56 s / 1085456384, medians 4.39 s and
1105379328; `full-0` and `w3-0b` as stated. The medians are correctly
computed from the three kept values. The W3-only and full runs have
distinct wall and RSS signatures (2.2-3.8 s / 397-477 MB against
4.4 s / 1.09-1.11 GB), which corroborates that the W3 rechecks checked
a reduced file, as the brief ordered.

The type claims the report makes about `coverIndex` and `packagedCover`
are proven by the exit-0 runs themselves: the full file, which contains
them, typechecked three times.

## QUESTION 3. IS THE ENUMERATION COMPLETE?

**Yes.** Against every enumeration the brief demands:

- `## WHAT COVER STILL OWES` restates `[LJ-1.484]`'s four steps, marks
  step 4 UNBUILT, and answers step 2's question ("It does not now
  matter for this step", `lj-1.487-report.md:197-198`). It does not
  claim `cover`.
- D-10 weighs both routes before any Agda and names the route taken
  (`lj-1.487-report.md:95-131`).
- W8 names what the orthodox argument uses, at `dev/literature/devlin-II5.md:107-108`,
  and gives the reason it does not stop as a literature NO-GO.
- W3 is checked alone, obligation omitted, with three forced rechecks
  and both medians, for W3 and for the full file.
- W2 is answered at the generic carrier; W4 is answered (nothing
  retired); the working-tree description matches `git status`: only
  `agents/tasks/LJ-1-487/` is new, `src/` untouched.
- "What this task does not settle" (`lj-1.487-report.md:339-347`) and
  "What the next brief needs" (`:349-374`) close the enumeration.

No section the brief requires is missing, and no built object is
claimed that the runs do not show.

## THE ATTACK ITSELF: FOUR QUESTIONS

1. **Correct on its own numbers?** Yes. One obligation, zero built,
   meter 1 UNRESOLVED of 1, exit 0. The NO-GO does not overclaim: it
   says twice that it is an obstruction of two routes and not a
   refutation of the type (`lj-1.487-report.md:178-179`, `:344`).
2. **Is the measurement sound?** Yes. The kept transcripts carry the
   `Checking` line, the `.time` files carry the numbers, the medians
   are right, and the caliber is the pane's
   (`runs/accept-1.out`, `GHCRTS -A64m -I0 -M8g`). The W3 claim is a
   term in an exit-0 file, which is the strongest form the tree
   accepts.
3. **Did the brief cause the outcome?** No. The brief ordered the one
   open step and forbade the two weakenings (postulate; second
   truncation). Both routes it offered are genuinely blocked at this
   telescope: route 1 by the formula-type meeting `[LJ-1.462]`
   measured (`agents/tasks/LJ-1-462/lj-1.462-report.md:77-79`) plus
   the undischarged Sat; route 2 by
   the absence of `M ≺_{Σ₁} L_lam` at `Formula CS.S` at the abstract
   telescope, the tree's inhabitant needing a canonical-code `f`
   delivered only at concrete sites
   (`src/L/BoundedSubset.lagda.md:1543-1545`). The brief did not
   foreclose a reachable GO.
4. **Is there a cure the return missed?** None I can find. A uniform
   bound cannot serve: `X` is an arbitrary subset of `Lset lam` at
   this telescope (`Probe487.agda:63-64`), so no single `γ ∈ M` covers
   every member. The `wit` route needs Sat of the packaged covering
   formula at `AbsL.𝒮M`, which is exactly the meeting `[LJ-1.462]`
   measured; the elementarity route needs the canonical-code instance
   at the abstract telescope, which the tree does not deliver. The
   return names both gaps correctly.

## THE W8 JUDGEMENT

The return's refusal to stop as a literature NO-GO is sound. The W8
stop condition fires when the shape is an axiom with no condition this
tree meets. This tree meets conditions: definable-existence closure
(`src/L/Hull.lagda.md:120-123`) and Σ₁ elementarity under canonical
codes at a concrete hull (`src/L/BoundedSubset.lagda.md:759-760`,
`:1543-1545`). What is missing is that machinery at this telescope and
this language, which is a route obstruction and not a literature
refutation. I also checked the errata: `dev/literature/devlin-II5.md:32`
pins the errata territory as not reaching II.5, and
`dev/literature/devlin-errata.md` carries no entry on II.5's covering
transfer. The literature basis of the report stands.

## VERDICT

**Upheld.** The NO-GO of LJ-1.487#1 agrees with its own body, every
load-bearing citation resolves today, and the enumeration is complete.
One cosmetic defect found (the `reverse` range off by one line) and it
carries nothing. The obligation stays open: `CoverWitnessesInHull` is
unbuilt, and the return's named gaps, Sat of `packagedCover` at the
stage semantics and the unfilled `Vec Code`, are the honest frontier.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: not read, declined. Retired per-episode
  journal; the record of this task is this directory.
- `archive/dev/ORCHESTRATION.md`: not read, declined. Retired
  orchestration history; this review judges one return, not a route.
- `archive/dev/DD-archived.md`: not read, declined. The DD clauses that
  bind here (W2, W4, W8) are restated in the live slot file and brief.
- `archive/dev/PLAN-archived.md`: not read, declined. Retired plan; the
  live plan is the queue and the screen.
- `dev/ARCHIVE.md`: not read, declined. Nothing was retired by the
  return under attack, so no archive row is in question.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`.
  Read at `:107`. Quote:
  `The reverse inclusion M ⊆ ⋃_{γ<β} L_γ runs the same transfer on the`.
  Read at `:108`. Quote:
  `statement "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" (`dev2.txt:1245-1290`). Finally`.
  Read at `:32`. Quote:
  `not reach II.5 (`devlin-errata.md:125-140`). Section 7 of this digest`.
  Used: to confirm the orthodox transfer the report names, and that the
  errata territory does not reach it.
- `dev/literature/devlin-errata.md`: read at `:1`. Quote:
  `# Devlin errata: documented error classes (do-not-repeat checklist)`.
  Used: checked for an erratum on II.5's covering transfer; none is
  listed.
- `dev/literature/BIBLIOGRAPHY.md`: not read, declined. No source beyond
  the digest is at issue in this review.
- `dev/literature/digest.md`: not read, declined. The rud route is not
  under attack here.
- `dev/literature/geology.md`: not read, declined. Stratigraphy of the
  literature corpus is not load-bearing for this review.
