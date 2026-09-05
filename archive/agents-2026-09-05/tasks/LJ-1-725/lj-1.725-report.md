# LJ-1.725 report — `carved-is-hier` from `table-sat`

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.725
obligation: agents/tasks/LJ-1-725/Probe725.agda::carved-is-hier
verdict: **NO-GO, STATED.** The name `carved-is-hier` is not inhabited.
`review-of-carved-is-hier.md` states the stop. What IS delivered and
green: `table-sat` as the hypothesis type (Probe725.agda:82-87), the
first inclusion `hierL-into-carved` (:100-113), the full member-reading
`carved-member-read` (:144-224), the stated residual `stage-read`
(:251-258), and both assemblies `carved-into-hierL-from` (:265-283) and
`carved-is-hier-from` (:286-299). The obligation closes from
`table-sat` plus exactly one input the tree does not carry.

The delivered probe TYPECHECKS: `runs/p-24.out`, EXIT=0, 23.55 s,
799,539,200 bytes peak, one Agda process, caliber `-A64m -I0 -M2g`
printed in the run. No heap wall: 37 percent of the 2,147,483,648-byte
wide cap. Nothing is postulated, the probe carries `--safe` and no
hole, nothing lands in `src/`. In-file line count 310, in-fence lines 0
(raw `.agda`), so the ratio bar cannot fire on it.

**A resumed dispatch.** This task was dispatched once before and
interrupted mid-flight. I resumed from its files: it left a probe with
one precedence error (`runs/p-11.out`), a report skeleton, and no
review file. Everything below was re-measured in THIS dispatch; the
prior runs `floor-1..9`, `p-10`, `p-11` stay in `runs/` as the record.

## 0. THE PREDECESSOR QUESTION

| piece | taken from | verdict there | use here |
|---|---|---|---|
| the obligation's type | agents/tasks/LJ-1-704/LJ-1.704.md (THE OBLIGATION) | 704 stated it and did not inhabit it | the target of this dispatch |
| `Carved`, `recordedFo` | agents/tasks/LJ-1-698/Probe698.agda:107-123, :87-88 | 698 GO as far as the door | the frame, imported |
| the hypothesis `table-sat` | the brief, typed as [LJ-1.724]'s obligation | 724 runs beside this task | stated at Probe725.agda:82-87, not inhabited |
| `through-door-closed` | agents/tasks/LJ-1-707/Probe707.agda:56-58 | 707 GO as an assembly | the consumer this GO would have served |

`[LJ-1.724]`'s brief is not in this worktree, so the hypothesis type
follows the brief's own sentence: membership written with `_∈_` on `V`,
which is `𝒮ᵥ`'s `∈ˢ` by definition (`src/V/Hierarchy.lagda.md:83`).

## 1. WHAT WAS BUILT

1. `table-sat` (:82-87). The hypothesis, verbatim per the brief.
2. `hierL-into-carved` (:100-113). REAL. A member of the table is
   `pr c (Lset c)` for `c ∈ γ` (`Recorded`, src/L/Hierarchy.lagda.md:497);
   `table-sat` puts that pair in `carved` directly.
3. `carved-read` / `carved-member-read` (:134-224). REAL. A member of
   `carved` reads as `u ∈ γ`, `z ∈ Lset γ`, the pair equation through
   `prAtL-adequate` (src/L/Coding/Model.lagda.md:125-130), and one
   residual conjunct: the satisfaction of the RELATIVIZED tower graph.
4. `stage-read` (:251-258). STATED, NOT INHABITED. The precise shape of
   the missing input.
5. `carved-into-hierL-from` (:265-283), `carved-is-hier-from`
   (:286-299). REAL. From `table-sat` AND `stage-read`, the equation
   closes. The distance from the brief's target is exactly one lemma.

## 2. THE FLOOR, MEASURED BEFORE ANY PROOF

This task inherited the floor rule; the frame was measured by running
the file with the hard part absent, and the measured floor is the
whole file's check, because every delivered row is an assembly of
landed readings with no new induction:

| run | wall | peak | note |
|---|---|---|---|
| floor-1 (prior dispatch) | 25.79 s | 805,781,504 B | first full-cone pass |
| p-12 | 371.64 s | 1,088,864,256 B | first deep pass; precedence bug fixed |
| p-24 (verdict) | **23.55 s** | **799,539,200 B** | EXIT=0, green |

The 350-380 s passes were NOT intrinsic: they were the elaborator
thrashing on constraints about the frame's stage `bound-of γ oγ hγ
.fst`, a stuck compound. Once the extraction was moved into a
σ-quantified module (`Fib`, :152-175), the same content checks in
23.55 s. Highest peak 1,088,864,256 B = 51 percent of the cap. No
heap wall was met and no run timed out.

## 3. WHERE THE SHAPE RESISTED

Three real defects, each fixed and each re-tested as a new shape
(p-12 to p-24; no failing run was ever repeated unchanged):

1. **Operator precedence** (:138 before the fix). `_×_` binds tighter
   than `_≡_`, so `w ≡ pr … × Σ…` parsed as `w ≡ (pr … × Σ…)`. The
   equation needed its own parentheses. This was the state the
   interrupted dispatch left.
2. **The fiber at a stuck stage** (:144-224). `∈-asFiber` at
   `{b = Lset Cγ.σ}` made Agda first report unsolved metas
   (`runs/p-19.out`: the unifier cannot invert the stuck `case` in
   `V-repr`), then terminate abnormally with explicit implicits
   (`runs/p-20.out`, `p-21.out`: `command terminated abnormally`,
   EXIT=1). Cured by restructuring: the extraction is defined ONCE in
   the σ-quantified module `Fib` (:152-175), whose constraints solve at
   a neutral stage exactly as Separation's own proofs do
   (src/L/Axioms/Separation.lagda.md:303-326), and instantiated at the
   frame afterwards (:185).
3. **Misdirected transports** (:281-283, :291-298). One `subst` ran
   the wrong way (`hier-in` proves membership at the pair term, so the
   transport needs `sym`); one pattern bound the pair-equation where
   the graph satisfaction was wanted; one ⊓-destructure bound the
   whole truncated satisfaction as one component.

## 4. W3, THE WIDEST UNMEASURED TERM, ANSWERED

The brief's W3: whether `Recorded` and `carveSat` give both inclusions
once table entries sit in `carved`. Answer: **the first inclusion yes,
the second no** — it costs `stage-read`, and the tree's gap is NOT the
syntax bridge. `relativize-correct`
(src/FOL/Manipulation/Relativize.lagda.md:142-143) already turns the
residual conjunct into the `A`-bounded semantics at `A = Lset γ`. What
is missing is the un-guarding spine back to the unbounded readings
`Lset-only` (src/L/Hierarchy.lagda.md:334-337) and `approx-val`
(src/L/Hierarchy.lagda.md:274-277) consume: every unbounded ∀ of the
graph (`domAt`'s at src/L/Coding/Base.lagda.md:278-279, `ApproxAt`'s
two, `extAt`'s at src/L/Coding/Sequence.lagda.md:119-120) instantiates
at members of members of `A`. That needs set-transitivity of
`Lset γ` as a set — assemblable from `Lset-out`
(src/L/Constructible.lagda.md:346) and `Lset-mono`
(src/L/Constructible.lagda.md:365) but not landed as one lemma — plus
a bespoke conversion over the whole formula. Price: above the brief's
40-to-90-line W3 estimate; the assemblies alone cost 190 in-file lines
and the spine is a new content lemma, not an assembly.

## 5. W2 ANSWER

The mathematics is written once at the generic carrier and
instantiated: the extraction module `Fib` (:152-175) is stated at a
quantified stage, quantified formula, and quantified Δ₀ witness, and
the frame instantiation is three arguments (:172). Both inclusions
reuse the landed generic readings (`Recorded`, `imageOut`,
`prAtL-adequate`, `hier-in`, `Lset-only`) and nothing is duplicated
against a sibling proof. `stage-read` itself is stated once at the
frame's telescope (:251-258). No deadline forced a fixed form.

## 6. WHAT THE NEXT BRIEF NEEDS

1. Fund `stage-read` in two halves, per the corrected target in
   `review-of-carved-is-hier.md`: first `Lset-trans-set` (members of
   members of `Lset γ` lie in `Lset γ`), then the un-guarding spine.
   `carved-is-hier-from` (Probe725.agda:286-299) is the consumer; the
   moment `stage-read` lands, `[LJ-1.707]`'s identification hypothesis
   becomes a report.
2. Do not re-fund the syntax bridge (`relativize-correct` is landed),
   another Δ₀ check of `relativize`, or another census of the graph's
   constants. All three are green in this probe.
3. `table-sat` stays `[LJ-1.724]`'s to deliver; its verdict decides
   whether `carved-is-hier-from` is inhabited as an assembly now.
4. Pass to every probe that reads `carve` members: extract fibers in a
   σ-quantified module, never at the frame's stuck stage (section 3
   above). This is a measured cure that transferred from Separation's
   own shape; it is proposed as a coder-clause candidate.

## 7. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 23.55 s (`runs/p-24.out`) |
| peak, verdict run | 799,539,200 B, 37 percent of cap |
| runs this dispatch | p-12, p-13, p-14, p-15, p-16, p-17, p-18, p-19, p-20, p-21, p-22, p-23, p-24, conetest-1, conetest-2 |
| in-file / in-fence lines | 310 / 0 (raw `.agda`) |
| brief estimate | 40 to 90 lines (W3) |
| caliber | `-A64m -I0 -M2g`, never set here |
| heap wall | none |
| `src/` edits | none |

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This dispatch resumed a live probe and measures its own assembly; no archived dispatching rule bears on it.
- `archive/dev/DD-archived.md:1` `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`. Declined: not used. The live homes of the coder clauses are the slot file and the brief, not this archive.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not used. The live screen is `dev/pod/screen.toml`; this task follows it.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not used. The route this task sits on is the live queue's, not the archived table's.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the \`L3.32-T\` series`. Declined: not used. The `L3.32-T` series predates the POD and shares no obligation with LJ-1.725.

## LITERATURE USED

- `dev/literature/level-formula-slot-roles.md:4` `as a formula? How many slots does the formula use? Which does it bind? Which`. Read. The probe's whole graph conjunct is a slot-reading question (`LsetGraphAt zero (suc zero)` at environments over the coded stage), and this file is the standing record of which slots the level-hood formulas bind.
- `dev/literature/devlin-errata.md:86` `- Build (p. 59): the definition admits "junk" (sequences with extra atomic`. Read. The junk-admission class is exactly why the reverse inclusion cannot shortcut the graph conjunct: a wrong `z` with the right pair equation is junk the bounded reading does not exclude, which is what `stage-read` must rule out.
- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used. A raw `.agda` probe carries no translation surface.
- `dev/literature/BIBLIOGRAPHY.md:1` `# Bibliography for the rud route`. Declined: not used. The rud route is not this route.
- `dev/literature/fine-structure.md:1` `# Fine structure: projecta, standard codes, the reductions, and their dependencies`. Declined: not used. Projecta and standard codes play no role in the identification measured here.
