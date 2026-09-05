# LJ-1.394 report: the ambient descent, and what the negation of `AmbCard` delivers

slot: `coder`. Written early as a skeleton and filled as answers landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-394/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time, no heap event.

TARGET: build TWO terms in `agents/tasks/LJ-1-394/Probe394.agda`, at a
GENERIC ordinal, and split `not-ambcard-gives` into its two steps.

## VERDICT

**GO on `descent-amb`. NO-GO on `not-ambcard-gives`, stated cleanly, and
the NO-GO is the measurement this task was dispatched for.**

1. **`descent-amb` is GREEN** at `Probe394.agda:96-119`, at a generic
   ordinal, with the descending arrow as an ambient injection. Median
   wall 1.49 s against a floor of 1.48 s (section 6). **The four-arrow
   composite costs nothing at this site.**
2. **STEP 1 is YES.** `lem` reaches the ORDINAL, merely:
   `amb-gives-merely` at `Probe394.agda:144-154`, green.
3. **STEP 1B is YES, and it is stronger.** The tree's own selection
   device reaches the ORDINAL as DATA, untruncated, with a least-code
   certificate: `amb-gives-ord-data` at `Probe394.agda:189-206`, green.
4. **STEP 2 is NO.** NOTHING reaches the ARROW. The one failing step is
   the hole at `Probe394.agda:249` inside `untrunc-amb` (`:247-249`):
   double-negation elimination at the ambient injection type, which is
   not a proposition. The file's ONLY error is that unsolved meta
   (`runs/full-with-hole.out`, exit 42). The full statement of the
   obstruction, with every citation, is
   `review-of-not-ambcard-gives.md`, written for the branch
   `no-go-stated`.

**THE BOUNDARY THIS LEAVES, IN ONE SENTENCE.** The negation of
`AmbCard` delivers the ordinal, merely by `lem` and as data by the
tree's own least-of device, and it delivers the injection only as a
double negation; so the recursion's case split needs codes at exactly
the ARROW and nowhere else on the negative side. That is the bill the
brief said a NO-GO would earn, and it is now priced against ONE step.

## 1. THE STATEMENT, AS THE TREE TAKES IT

The two obligations are stated verbatim from the brief. `descent-amb`
at `Probe394.agda:96-98` and `not-ambcard-gives` at `:251-255`. The
brief's conclusion line writes `⟨ ω ∈ β ⟫`; the bracket is a typo for
`⟨ ω ∈ β ⟩`, which is what the file writes.

`AmbCard` (`:64-66`) is `[LJ-1.393]`'s notion, stated here LOCALLY
because that probe had not landed when this file was written. It has
landed since, and its `AmbCard`
(`agents/tasks/LJ-1-393/Probe393.agda:74-77`) is textually identical
to this file's, so the local statement stands.

One reading note the next brief needs. **The hypothesis of
`not-ambcard-gives` is ONE negation**, `(AmbCard α → Empty.⊥)`, and not
two. My first typing of STEP 1 carried two negations and the type
checker refused it immediately; the corrected single-negation typing is
the green one at `Probe394.agda:145`. The brief's text "It takes a
NEGATION" is correct; the reader of the signature must count the
parens.

## 2. `descent-amb`: THE FOUR ARROWS

**I PORTED `mem-incl` verbatim, the 12 lines of
`agents/tasks/LJ-1-390/Probe390.agda:76-89`, now at
`Probe394.agda:68-81`.** No re-derivation was needed; the term was
already at plain `V ℓ`, which is where this task works.

The composite at `:96-119` is `[LJ-1.390]`'s `descent-core`
(`agents/tasks/LJ-1-390/Probe390.agda:110-131`) with two differences,
both required by this task's shape:

- the descending arrow is an AMBIENT injection `(⟪ α ⟫ ↪ ⟪ β ⟫)`, not
  a code read back through a door;
- the inclusion arrow is `mem-incl`, not a variable.

**The [LJ-1.390] cost lesson was applied and did not appear.** That
probe measured 175.42 s for the same mathematics bound in one term with
the door inside the `where` (`agents/tasks/LJ-1-390/lj-1.390-report.md:172-179`),
and its cure was to take the descending arrow as a parameter. Here the
arrow IS a parameter of the statement, no door exists anywhere in the
term, and the whole composite runs at floor price (1.49 s against a
1.48 s floor). The cure held; the wall never came.

## 3. STEP 1: `lem` REACHES THE ORDINAL

`amb-gives-merely` (`:144-154`) takes `(AmbCard α → Empty.⊥)` and
returns `ex-amb α` (`:136-139`): a MERELY-existing `β` with `IsOrd β`,
`⟨ β ∈ α ⟩`, `⟨ ω ∈ β ⟩`, and the injection under a DOUBLE NEGATION.

The derivation spends `lem` once, on the proposition `ex-amb α` itself.
If `ex-amb α` fails, then every injection below `α` refutes the failed
existence, so `AmbCard α` holds, which contradicts the hypothesis
(`:150-154`). The `inl` branch is the witness. **The step needs neither
`oα` nor `ω∈α`**; those enter the consumer's recursion, not this lemma.

## 4. STEP 1B: THE SELECTION DEVICE REACHES THE ORDINAL AS DATA

This is the half the brief's "a least-of selection may apply" asked
about, and the answer is YES. `amb-gives-ord-data` (`:189-206`) returns
`Σ[ a ∈ Mem (Lset (sucV α)) ] Payload α (fst a)`, UNTRUNCATED.

The mechanism is `[LJ-1.314]`'s (`agents/tasks/LJ-1-314/CodeUntrunc.agda:75-101`)
re-measured at its own site, as the Boundary demands: `leastOf` over
`orderAt` at the stage `Lset (sucV α)`, whose carrier holds every
member of `α` by `ord-below-stage` (`:173-176`, layer transitivity).
The payload `Payload α β` (`:178-181`) is a proposition, all four
components (`:182-187`), so the device applies and even returns a
least-code certificate with the ordinal.

**The injection component of the payload is still a double negation.**
That residue is not removable by this device at any price, because the
device demands a propositional payload
(`src/L/WellOrder/Base.lagda.md:158-160`) and an injection is not one
(`src/L/Cardinal.lagda.md:47-48`). STEP 1B therefore measures the exact
reach of the tree's one untruncation device at this site: it reaches
the ordinal and nothing further.

## 5. STEP 2: NOTHING REACHES THE ARROW. THE OBSTRUCTION

**The failing step, at `Probe394.agda:249`.** Convert
`(((⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥) → Empty.⊥)` into `(⟪ α ⟫ ↪ ⟪ β ⟫)`. The
assembly around the hole is complete: `not-ambcard-gives`
(`:251-256`) is STEP 1 plus this one conversion, and it typechecks up
to the hole, with the hole the file's ONLY error.

**Why each device in the tree fails, with the citations, is in
`review-of-not-ambcard-gives.md`.** In short: `lem` decides propositions
(`src/Base/Classical.lagda.md:41-42`) and the injection is a `Σ` over a
function type; `leastOf` demands a propositional payload and orders
ordinals, never injections; the tree's one bridge runs coded to ambient
(`src/L/CantorBernstein.lagda.md:33-38`) and `[LJ-1.299]`'s `amb→code`
consumes the ambient face only to refute a code
(`agents/tasks/LJ-1-299/NoInj2.agda:103-111`), so it is not the missing
bridge either.

**THE SWEEP (C-42).** `grep -rn "∥.*↪" src/` gives 9 lines; 4 carry
this task's shape, all inside one module, the least-cardinal search:
`src/L/Cardinal.lagda.md:113`, `:133`, `:141`, `:151`, whose own
comment at `:132` says "still truncated, still not an hProp". The
other 5 carry propositional payloads. **The NO-GO names one debt the
tree already held, and adds a second site to it.**

**I did not weaken the statement and I added no postulate.** The
truncated form of `not-ambcard-gives` was NOT built.

## 6. RUNS, FLOOR, SLOTS (C-53, C-12)

All runs on 2026-08-19, from the repository root, `agda --safe
agents/tasks/LJ-1-394/Probe394.agda`, `GHCRTS="-A64m -I0 -M8g"` (the
program's pane caliber, never changed by me), ONE Agda process at a
time, no parallel runs, no heap event. Each row is the probe truncated
or extended to hold exactly what the row names; logs are in `runs/`.

| row | contents | 3 consecutive walls | median |
|---|---|---|---|
| 1 | imports only, no term (FLOOR) | 1.51 / 1.44 / 1.48 | **1.48 s** |
| 2 | row 1 + `AmbCard`, `mem-incl` port, `descent-amb` | 1.63 / 1.49 / 1.49 | **1.49 s** |
| 3 | row 2 + STEP 1 (`amb-gives-merely`) | 1.52 / 1.44 / 1.43 | **1.44 s** |
| 4 | row 3 + STEP 1B (`amb-gives-ord-data`) | 1.53 / 1.51 / 1.43 | **1.51 s** |
| 5 | row 4 + STEP 2 hole + the assembly | 1.50 / 1.50 / 1.51 | **1.50 s**, exit 42 |

**WHAT THE TABLE SAYS.** Every term of this probe is FREE at this site;
all medians sit inside the floor's own spread, and no row shows the
`[LJ-1.390]` explosion. The brief priced `descent-amb` at
about 20 code lines on a shape-comparable basis
(`agents/tasks/LJ-1-390/Probe390.agda:110-131`); the delivered term is
30 lines including its signature and the `mem-incl` application, and it
cost no time at all. `not-ambcard-gives` was UNPRICED by the brief and
it stays so: the missing step is a PRINCIPLE and not a quantity of
lines, which is itself the finding.

**RE-DISPATCH RE-MEASUREMENT.** The task came back to the coder slot
once, to repair this report's survey answers and nothing in the probe.
The probe ran again while the task was live, same day (2026-08-19),
same machine, same caliber, three consecutive runs each: the floor
(imports only) 1.43 / 1.38 / 1.50, median 1.43 s, green; the standing
file with the hole 1.56 / 1.73 / 1.50, median 1.56 s, with the ONE
unsolved meta at `Probe394.agda:249.19-20`, and no heap event. Both
medians sit inside the table's own spread, so no standing number
moves. The probe file is byte-identical to the attempt-1 file (sha256
`2fe9c4768707e5fe05c81ff15300c03f6fedc90a503b8a824bc5dd8fbc8e2b66`).
Logs: `runs/floor-2.out`, `runs/standing-2.out`.

## 7. W2 AND DD4: WRITE IT GENERIC

Both obligations are generic in the ordinal. The module
`LJ-1-394.Probe394` (`Probe394.agda:39`) takes only `ℓ` and `lem`; no
term names a site, a stage, or a numeral; `descent-amb` is at generic
`α β`, `not-ambcard-gives` at generic `α`. W2 answered.

## 8. WHAT GO AND NO-GO EACH EARN, AND THE RECOMMENDATION

**The GO half closes its side of the case split.** With
`descent-amb`, the recursion of `[LJ-1.395]` consumes the negative case
in four arrows and at floor price, PROVIDED the case split hands it an
honest ambient injection and an `sq β`.

**The NO-GO half prices the case split, and the price is codes at the
ARROW only.** My RECOMMENDATION to the mathematician, and it is a
recommendation and not a ruling: the truncated form of
`not-ambcard-gives` does NOT serve this recursion, because `descent-amb`
itself consumes an honest `(⟪ α ⟫ ↪ ⟪ β ⟫)` and `sq α` is untruncated
data, so a truncated injection dies one step later at the composite.
The form that serves is `[LJ-1.390]`'s OWN residue shape: a CODED
injection in the case split, untruncated by the same device STEP 1B
re-measured, then read back by `code-untruncates`
(`agents/tasks/LJ-1-386/Probe386.agda:264-268`) into the ambient arrow
`descent-amb` eats. The recursion would then carry codes at exactly the
case split and nowhere else, which is the smaller bill the brief named.

**The archive agrees with the direction.** The retired route delivered
a TRUNCATED square law at initial ordinals
(`archive/dev/TASKS-archived.md:82`) and never an untruncated one; its
catalog says the least-of witness stays "only up to truncation, and no
canonical bijection exists to make it honest"
(`archive/src/2026-08-09-rud-route/Everything.lagda.md:307-308`). My
NO-GO is at a different site and a different noun (an INJECTION from an
ambient negation, not a bijection), so the two walls do not collide,
but they point the same way.

## 9. ARCHIVE USED

I ran this survey after the probe's green stages and before the return.

- `archive/src/2026-08-09-rud-route/Everything.lagda.md:307-308`.
  **BEARS as the nearest recorded wall.** The lines read "the least-of
  search returns its witness only up to truncation, and no canonical
  bijection exists to make it honest". The noun there is a canonical
  BIJECTION. My hole is an untruncated INJECTION from an ambient
  negation. `[LJ-1.386]`'s door delivers an untruncated injection from
  a CODED existence, so the archived wall does not cover that door, and
  my site adds the ambient-side datum: the boundary runs BETWEEN THE
  GRADES of the hypothesis, coded yes, ambient no.
- `archive/dev/JOURNAL-archived.md:1732`. **BEARS as the same limit in
  the campaign's words**: "The untruncated equivalence remains
  unavailable (T31's wall)". An equivalence is not an injection; the
  wall stands after my measurement.
- `archive/dev/TASKS-archived.md:82`. **BEARS on section 8's
  recommendation**: the row reads "Truncated square law at initial
  ordinals | DELIVERED", so the retired route's square law was
  DELIVERED only in truncated form, and the wall at the call site was
  confirmed at `archive/dev/TASKS-archived.md:78`, whose row reads
  "Where counting calls the square law | RED (wall confirmed)".
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`. Not
  used: the condensation crossing of the retired route, level-hood
  recognition at a transitive carrier. It carries no selection device
  and no untruncation; the only "truncat" hits in the file are the
  `PropositionalTruncation` import at its line 65 and a code-style
  comment at its line 651, so nothing in it bears on this task.
- `dev/ARCHIVE.md` and `archive/dev/DECISIONS-archived.md`: searched;
  no entry names an untruncation at an ambient function-typed payload.

## 10. LITERATURE USED

- `dev/literature/truncation-and-selection.md:335-337`. **BEARS
  directly on STEP 2**: "A canonical injection needs a well-order on
  the INJECTIONS, which is what `<_L` supplies classically and what an
  ambient function type does not have." That is the criterion the hole
  measures: the ordinals below `α` are well-ordered, the injections
  between them are not, and no tree device orders them.
- The same file's section 5, item 3, says whether a trophy statement
  must carry data rather than a truncation "is the owner's". I left the
  obligation failed and put the form question in section 8 as a
  recommendation, as the brief instructed.
- `dev/literature/devlin-II5.md`. Not used: the condensation lemma and
  the GCH in L. Level-hood recognition holds nothing on truncation or
  selection; a grep for "truncat", "select" and "injection" over the
  file gives no hit.
- `dev/literature/devlin-errata.md`. Not used: a do-not-repeat
  checklist of documented error classes in the two named accounts. No
  entry names a selection or an untruncation device; a grep for
  "truncat", "select" and "untrunc" gives no hit.
- `dev/literature/digest.md`. Not used: the orthodox FORM of the rud
  route. This task measured a tree device at a tree site, and the form
  of the route is not what failed here.
- `dev/literature/geology.md`. Not used: set-theoretic geology sources
  (mantles, grounds, Hamkins, Usuba). Not this subject.

## WHAT I DID NOT DO

- I did not weaken `not-ambcard-gives`, did not add a postulate, and
  did not build its truncated form.
- I did not touch `src/`; `src/` is forbidden for a probe.
- I did not import `[LJ-1.393]` (it had not landed when this probe was
  written), so `AmbCard` is local; the two statements are identical by
  text.
- I did not run `make check`; no file outside this task's directory
  changed, and the probe is not in `src/`.

## GATES RUN ON MY FILES

`agda --safe agents/tasks/LJ-1-394/Probe394.agda` is the only checker
this task has (it lives outside `src/`). It was run at every stage;
row 5 of section 6 is the standing result: ONE unsolved meta at
`Probe394.agda:249`, exit 42, by design.
