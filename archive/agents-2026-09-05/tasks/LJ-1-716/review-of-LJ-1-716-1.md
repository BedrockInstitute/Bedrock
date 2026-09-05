# LJ-1.716: adversarial review of LJ-1.716#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
task: LJ-1.716
review_of: agents/tasks/LJ-1-716/lj-1.716-report.md
verdict: upheld

## What I attacked, and how I re-measured it

I read the brief (`agents/tasks/LJ-1-716/LJ-1.716.md`), the return
(`lj-1.716-report.md`), the return's NO-GO statement
(`review-of-ambient-at-hier.md`), the probe (`Probe716.agda`), and the
acceptance arm (`runs/accept-1.out`). `dev/pod/transitions/2026-08.jsonl`
in this worktree carries NO line with `"task": "LJ-1.716"`: the tracked
file ends at this worktree's base (last line seq 4839, a STOPPED event at
2026-08-27T09:45:14Z), before the task ran. So I could not read `model`,
`effort` or `heads_sha256` for this task, and I do not infer them. The
accept arm carries the six facts I attack on: rc 42, 3.29 s, error class
`unsolved_meta`, obligations delta 0, in-fence lines 0, heap wall false.

I re-ran the probe myself, read-only, same caliber, output to stdout. My
run reproduces the final state exactly: the ONLY errors are the two
designed holes, at `Probe716.agda:131.18-69` (`zero-refutes`' plug) and
`Probe716.agda:144.24-147.58` (`ambient-at-hier`), identical to
`runs/p-10.out` and `runs/p-11.out`. Both green lemmas re-measure green
today. I wrote and touched no `.agda` file (A21): my one measurement was
re-running the predecessor's own artifact, and where a stronger check is
wanted I name the probe below and stop there.

The load-bearing chain, re-verified at source:

1. `matrix₃ = isOrd-at-p ∧̇ φ₃` and `φ₃ = W3.erased`
   (agents/tasks/LJ-1-667/Probe667.agda:70-73, :46-48).
2. `W3.three` wraps `Mx.matrix` in twelve `∃̇∈` and each wrap bounds by
   `var (lastFin {n})`, the LAST slot; at arity 3 that slot is the
   witness `z` (agents/tasks/LJ-1-667/runs/W3.agda:56-57, :69-79).
3. Bounded-existential satisfaction is a join that forces a member of
   the bound: `γ ⊨ (∃̇∈ t φ) = ⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ))`
   (src/FOL/Semantics.lagda.md:103). So any satisfaction of `matrix₃` at
   `(a, p, z)` forces a member of `z`.
4. The obligation fills `z` with `fst (hierL (fst δ) (δ .snd) oδ)`. At
   `δ₀ := (∅ , ∅∈L)` the table has no members: `IsHier B h` makes
   membership equal `Recorded B`, and `Recorded` joins over
   `fst c ∈ B` (src/L/Hierarchy.lagda.md:494-503), empty at `B := ∅`.
   `no-member-of-hierL∅` (Probe716.agda:82-96) machine-checks this.
5. `ambient-at-hier-empty` (Probe716.agda:109-115) peels the first
   member off any reading, generic in `δ` and `oδ`. A `Π` obligation dies
   by one counterexample, so `δ₀` kills the whole type.

The claim is not "not yet proved": the obligation is FALSE at `δ₀`, and
both halves of the refutation are green in my own run.

## Question 1: does the verdict LINE match its own BODY?

YES. The LINE says NO-GO, target false at `δ₀`, "machine-checks the
refutation in two green lemmas". The BODY states in the same breath that
the composition `zero-refutes` and the obligation itself are designed
holes, and that only the bookkeeping composition is unverified
(`review-of-ambient-at-hier.md`, section "The site, and the falsity":
"The mathematics is fully machine-checked; only the bookkeeping
composition is not."). The LINE's phrase is scoped by the BODY; nothing
in the LINE claims more than the BODY delivers. The accept arm agrees
with the BODY: rc 42 on the two holes only, obligations still open. The
coder's `review-of-ambient-at-hier.md` sits in the brief's own SCOPE and
is the shape branch `stop-stated` names, so it is not a foreign file and
not an F9 defect: the critic here is me, not the author.

## Question 2: is every load-bearing claim backed by a `file:line` that resolves today?

YES on every load-bearing claim; NO on four secondary pointers, which I
corrected and re-verified. Every file resolves; four line pointers miss
their targets:

| Cited | Claim | Found at | Material? |
|---|---|---|---|
| agents/tasks/LJ-1-520/Probe520.agda:122-135 | `pins` fixes the tags to the numerals | :108-112 (`pins`), :115-121 (`Δ₀-pins`); :122-135 is the matrix assembly | No: the claim is true at the corrected lines, and the δ₀ refutation needs only the FIRST existential, no pins |
| agents/tasks/LJ-1-673/Probe673.agda:46-47 | `countFo matrix₃ ≡ 0` by `refl` | the `refl` is agents/tasks/LJ-1-667/Probe667.agda:52-53; :46-47 is the comment stating it | No |
| dev/literature/level-formula-slot-roles.md:23 | Devlin 5.2 (a) row 4 | row 4 is at :26; :23 is the Devlin 2.4 row | No: quoted content exists, at :26 |
| agents/tasks/LJ-1-673/Probe673.agda:74-77 | `inBound` leaves its existentials unbounded | :83-89 (`∃̇ (∃̇ …)`, unbounded); :74-77 is `matrix₃-Code` | No: claim true at :83-89 |

The load-bearing citations are all exact: Probe667.agda:46-48 and :70-73,
runs/W3.agda:56-57 and :69-79, src/FOL/Semantics.lagda.md:103,
src/L/Hierarchy.lagda.md:494-503 and :646-653, src/V/Coding.lagda.md:175-176
(`pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆`), src/L/Constructible.lagda.md:141-143
(`IsOrd`'s two components), Probe652.agda:87-91 (witness slot free in
`Witnessed`), Probe673.agda:108-109 (the briefed type). Four sloppy
pointers are a hygiene defect, not a verdict defect; none flips anything.

One number needs a precise reading. The report says the plug "walls the
checker at 2.6 to 2.7 g near 300 s". The .outs say the run DIES at the 2 g
GHC heap cap: `agda: Heap exhausted; Current maximum heap size is
2147483648 bytes (2048 MB)`, EXIT=251, near 300 s, peak resident set
2.59-2.74 GB (runs/g-4.out, runs/vh-1.out, runs/vi-1.out, runs/p-7.out).
So 2.6-2.7 g is peak RSS at cap exhaustion, and the required heap is
UNKNOWN, only at least 2 g. The report never claims a larger cap
suffices; it books "a larger caliber" as a cure that needs funding. Read
that way, the claim is sound, and the greens vs walls split is
apples-to-apples: every run recorded `GHCRTS=[-A64m -I0 -M2g]`, greens at
3.2-3.6 s and 0.70-0.85 g, walls by heap exhaustion.

## Question 3: is the predecessor's enumeration complete?

YES for the verdict, with two consequences it did not state; neither
reopens the NO-GO.

Complete parts, verified: the brief's NO-GO menu (graph, erase,
`isOrd-at-p`, slot order) is answered item by item and all four are
cleared with true citations; the miss is named as the matrix's
witness-slot content, which the semantics at src/FOL/Semantics.lagda.md:103
supports directly. The C-42 sweep count of 1 is correct: the shape "tags
bounded by the table" occurs at this obligation alone; `inBound` binds
value and parameter by `≐` and leaves its existentials unbounded
(Probe673.agda:83-89), and `levelFo` binds all thirteen slots with
unbounded `∃̇` (agents/tasks/LJ-1-520/Probe520.agda:171-185). The wall
enumeration covers ten tested shapes with a measured split, and every
retry was a new shape as the wall protocol demands.

The two unstated consequences:

1. The any-ordinal falsity is PROSE, not measurement. `review-of-ambient-at-hier.md`
   argues "`∅` is not in the table at ANY ordinal" from never-empty
   Kuratowski pairs (src/V/Coding.lagda.md:175-176) plus the pins. That
   argument is plausible and cited, but no green lemma states it: the
   machine-checked falsity stops at `δ₀`. A21 sends this to the coder as a
   NAMED probe, not something I write: generalize the vacuity lemma to
   `(B : CS.S) → ⟨ isL B ⟩ → IsOrd B → ((c : CS.S) → ⟨ fst c ∈ B ⟩ →
   Empty.⊥)` on the table side, and pair it with a first-pin descent
   (the first existential's witness must satisfy `∀̇∈ (var N0) ⊥̇`, that
   is, be member-ful-free) to kill the reading at every `B`. One probe,
   same caliber; if it walls at the concrete instantiation, the
   variable-land form alone still upgrades the count.
2. The soundness residue goes vacuous at table readings. Probe667's
   Witnessed shape asks
   `(a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ matrix₃ ⟩ → a ≡ Lset p`
   (agents/tasks/LJ-1-652/Probe652.agda:87-91). With the reading false
   whenever `z` is the table, that half holds vacuously at such `z`; the
   witnessed direction must move to a slot that carries the numerals, or
   to the unbounded `levelFo` reading. The return's corrected-target
   paragraph already lands on exactly those two candidates, so no
   guidance changes; the vacuity note is for the next brief's framing.

On my lens question three, the brief did not cause the outcome: the
obligation type was fixed by the brief and is genuinely false, so NO-GO
was the only possible answer and the brief provided for it (branch
`no-go-stated`). One note for the queue, not a defect: premises 2 and 3
of the brief already cited both halves of the refutation
(Hierarchy.lagda.md:646-653, Probe667.agda:72-73), so a D-10 truth check
at brief time might have caught the `δ₀` falsity before spending the
slot. The slot was cheap: one 3.3 s probe settled it.

## Verdict

**UPHELD.** The NO-GO stands on its own numbers, re-measured by me today:
the obligation `ambient-at-hier` is false at `δ₀ := (∅ , ∅∈L)`, both
green lemmas re-run green, and the only holes are the two designed ones.
The four pointer defects and the prose-only any-ordinal claim are hygiene
findings; none changes the verdict. Per row `sys-critic-upheld-no-go`,
this file with exit 0 and the obligation still open
(`obligations_open: 1` in runs/accept-1.out) closes the task as
`done` / `no-go`.

## ARCHIVE USED

- archive/dev/DD-archived.md:35: `is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed.` Read. This is my lens, DD25's row, and I answered its four above.
- archive/dev/ORCHESTRATION.md: declined, not read. A pre-pod
  orchestration record; this review's protocol comes from my slot file
  and the brief, not from it.
- archive/dev/PLAN-archived.md: declined, not read. The live plan is the
  queue and the direction; no archived plan item bears on this refutation.
- archive/dev/measurements/README.md: declined, not read. I measured from
  the task's own runs/ artifacts; no archived measurement record bears.
- archive/dev/README.md: declined, not read. An archive index; no
  archived module is in this review's scope.

## LITERATURE USED

- dev/literature/level-formula-slot-roles.md:26: `∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]` Read. Row 4 is the outside view of the NO-GO: the literature BINDS the witness `z`, while `matrix₃` keeps it free and the obligation fills it with the table. I cite it at :26, where the row sits; the return's pointer said :23, which is the Devlin 2.4 row.
- dev/literature/BIBLIOGRAPHY.md: declined, not read. Cite-check only;
  the return already did that pass and my review cites no new source.
- dev/literature/devlin-errata.md: declined, not read. A do-not-repeat
  checklist for the rud route's Devlin accounts; this review quotes no
  Devlin prose.
- dev/literature/primary-sources.md: declined, not read. A source
  register; this review cites no primary source beyond the digest row
  above.
- dev/literature/glossary-review-2026-08.md: declined, not read. A
  glossary review; this review coins no term.
