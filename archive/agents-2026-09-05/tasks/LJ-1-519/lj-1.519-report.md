# [LJ-1.519] report: `hier-in-stage` at a limit

## 1. VERDICT

**W3 is a GO. The obligation is a STOP, and it is stated in
`agents/tasks/LJ-1-519/review-of-hier-in-stage-limit.md`.**

- W3 `two-below` is built and green. A limit supplies the intermediate `β`,
  and it supplies every finite number of steps at one application per step.
  The task did not stop at its cheapest point.
- `hier-in-stage-limit` is NOT built. No postulate stands in for it. The
  brief's type forms and is in the probe as `HierInStageLimit`
  (`agents/tasks/LJ-1-519/Probe519.agda:148`).
- What IS built is Devlin's own proof of 2.6(ii), total in `γ`, with his two
  stage bounds as hypotheses (`agents/tasks/LJ-1-519/Probe519.agda:235`).
- One WALL event. Section 6.

**The single finding: the limit buys the room, the room was never the
blocker, and the source does not prove the part that is.**

## 2. WHAT THE LIMIT BOUGHT

The brief requires this section as a deliverable "even if the obligation is
not built". Here it is, as types, all four green.

**BOUGHT, in full.** Successor closure, iterated:

    steps-stay : (γ : V ℓ) → ⟨ γ ∈ α ⟩ → (n : ℕ) → ⟨ step n γ ∈ α ⟩

`agents/tasks/LJ-1-519/Probe519.agda:200`. W3 is the case `n = 1`. Devlin
needs `n = 4`. The proof is one application of the limit hypothesis per step
and the cost does not grow with `n`.

**BOUGHT, in full.** The stage inclusion that follows:

    stage-below : (γ : V ℓ) → ⟨ γ ∈ α ⟩ → (n : ℕ)
                → {x : V ℓ} → ⟨ x ∈ Lset (step n γ) ⟩ → ⟨ x ∈ Lset α ⟩

`agents/tasks/LJ-1-519/Probe519.agda:208`. One `Lset-mono`.

**NOT BOUGHT, and not touched.** The two stage bounds:

    StageHigh = (γ : V ℓ) (oγ : IsOrd γ) → ⟨ ω ∈ γ ⟩
              → ⟨ fst (seq γ oγ) ∈ Lset (step 4 γ) ⟩

`agents/tasks/LJ-1-519/Probe519.agda:218`, with `StageLow` at `:225` for the
tail `γ ≤ ω` that Devlin's `δ > ω` excludes.

**IS IT ENOUGH FOR THE TWO STEPS? Yes, and that is the wrong question.**
`stage-below` MOVES a set that is already in a stage. `StageHigh` PUTS a set
into a stage. `two-below` and `steps-stay` answer the first completely and
the second not at all. The brief asks whether the limit is "enough for the
two steps". It is more than enough: it gives every finite number of steps.
The obligation still does not follow, because room is not what was missing.

## 3. D-10: WHAT THE TREE'S `IsLimit` IS

**The tree has NO `IsLimit`.** `grep -rn "IsLimit" src/` returns nothing.
This is the first thing the brief asked and the brief's obligation type names
`IsLimit α` as though it were delivered.

The limit hypothesis exists in `src/` only as a spelled-out closure under
successor, at two independent sites, and both have one shape:

- `src/L/InjChain.lagda.md:109`
  `ω-limit : (γ : V ℓ) → ⟨ γ ∈ ω ⟩ → ⟨ sucV γ ∈ ω ⟩`
- `src/L/SquareLawClosed.lagda.md:125`
  `kappa-limit : ... → ⟨ γ ∈ˢ fst (κL a oa) ⟩ → ⟨ sucV γ ∈ˢ fst (κL a oa) ⟩`

So the probe DEFINES the predicate at that shape
(`agents/tasks/LJ-1-519/Probe519.agda:55`) and re-ascribes both tree
witnesses to it as checked rows (`:62`, `:70`). A green row is evidence. A
comment is not.

**ANSWER TO D-10: yes, it gives a successor in `α` for each `β ∈ α`, because
that IS the tree's definition of it.** The D-10 stop condition the brief set
does not fire. The task continued, and the stop it reached is a different one
and it is in the source.

## 4. W3: THE TWO STEPS

    two-below : (α : V ℓ) → IsOrd α → IsLimit α → (γ : V ℓ) → ⟨ γ ∈ α ⟩
              → ∥ Σ[ β ∈ V ℓ ] (⟨ β ∈ α ⟩ × ⟨ γ ∈ β ⟩) ∥₁

`agents/tasks/LJ-1-519/Probe519.agda:85`. Built with `β := sucV γ`: the limit
gives `sucV γ ∈ α`, and `self∈sucV` (`src/V/Model.lagda.md:236`) gives
`γ ∈ sucV γ`.

**The truncation is not needed.** The limit hands over a CANONICAL witness,
so nothing is selected and nothing must be untruncated
(`dev/literature/truncation-and-selection.md:88`). The probe keeps the
brief's truncated type and wraps the witness. A later brief may take the
sharper untruncated form for free.

**The estimate was about 20 lines and under 35 seconds. The measurement is
2.27 seconds.** The brief said not to fund W3 against `[LJ-1.517]`'s census.
It was not funded against it, and the price is an order below the estimate.

## 5. THE REDUCTION, WHICH IS THE DELIVERABLE

`_build/literature/dev2.txt:676-678` gives Devlin's whole proof of 2.6(ii).
He reduces to `(L_γ | γ ≤ δ) ∈ L_{δ+4}` and then writes "We leave all the
details to the reader". The probe carries that reduction as a checked term:

    reduction : StageHigh → StageLow → HierInStageLimit

`agents/tasks/LJ-1-519/Probe519.agda:235`. It is TOTAL in `γ`: the
trichotomy `ord-tri γ oγ ω ω-ord` splits at `ω`, the two low branches go to
`StageLow` through `step 5 ω`, and the high branch goes to `StageHigh`
through `step 4 γ`. Every line of the body is section 2's "bought" column.

`seq γ oγ = hierL (sucV γ) ...` is Devlin's `(L_δ | δ ≤ γ)` in the tree's own
words, and the probe checks that rather than asserting it: `seq-spec`
(`agents/tasks/LJ-1-519/Probe519.agda:140`) gives
`IsHier (sucV γ) (seq γ oγ)`, and `Recorded`
(`src/L/Hierarchy.lagda.md:497`) is exactly the class of pairs
`(c , Lset c)` for `c ∈ sucV γ`. `sucV γ` is the ordinals `δ ≤ γ`. The
reading agrees with the outside view of the same formula
(`dev/literature/level-formula-slot-roles.md:24`).

**What this is worth to the next brief.** `StageHigh` carries no `α`, no
limit hypothesis and no `ω ∈ α`. Nine dispatches have been fighting a
statement with `α` in it. This one has no `α`. That is the whole gain and it
is real, but it does not make the residue easier, only smaller to state.

## 6. THE WALL

**One heap exhaustion. I report it and I did not simply rerun it.** The
caliber was the wide one the program set, `GHCRTS=-A64m -I0 -M8g`, one Agda
process per run, and every `src/` interface was already warm.

The brief's spelling takes `γ ∈ α` and no `IsOrd γ`, so ordinal hood must be
derived by `mem-ord`. I wrote that derivation as `derived`, a one-line body.
It exhausted the heap.

I ran the gutted-body experiment that `dev/LESSONS.md:2418` prescribes,
because `dev/LESSONS.md:2415` withdraws the statement-bound category and says
the cure must not be transferred by analogy. Four measurements:

| what | wall | peak RSS | evidence |
|---|---|---|---|
| the obligation TYPE alone, no term | 2.70 s | 474 MB | `runs/type-only.time` |
| `mem-ord` alone, value never fed to `seq` | 2.77 s | 477 MB | `runs/controls.time` |
| the application with `IsOrd γ` a HYPOTHESIS | 2.77 s | 477 MB | `runs/controls.time` |
| the COMPOSITION of the two, implicit inferred | 323.98 s | 9.08 GB, DIED | `runs/wall-derived.time` |
| the COMPOSITION, implicit given explicitly | 377.46 s | 8.93 GB, DIED | `runs/wall-composition.time` |

The last row rules out an unsolved metavariable as the cause. Neither factor
costs. The composition walls.

**ROOT CAUSE, and it is a fact about the tree and not about this probe.**
`seq` feeds its `IsOrd γ` to `suc-ord`, and `suc-ord` PATTERN-MATCHES the
pair: `suc-ord {A} (Atr , Amem) = ...` (`src/L/Ordinal.lagda.md:97`).
`isL-suc` destructures it twice more. A `mem-ord`-derived proof is an
`∈-induction` recursion (`src/L/Ordinal.lagda.md:222`). So destructuring it
runs that recursion inside the stage constructor's argument, at every
conversion check.

**CONSEQUENCE FOR THE STATEMENT.** The probe's `HierInStageLimit` takes
`IsOrd γ` as an explicit argument. That is a WEAKER statement to assume than
the brief's spelling, and I say so rather than hide it. It is not weaker to
conclude, and mathematically the hypothesis is free. It is not free to the
elaborator, and 8 GB is the price of making it free at this site.

**This is not a measured cure and I did not transfer one.** It is a measured
DISEASE at one site. `AGENTS.md:45` says a cure does not transfer by analogy,
and I make no claim about any other site that derives an `IsOrd` by
`mem-ord`. Whether the shape is elsewhere in the tree is a C-42 sweep and it
is not this task's scope.

## 7. PRICES

One Agda process per run, `GHCRTS=-A64m -I0 -M8g`, forced recheck by removing
`_build/2.8.0/agda/agents/tasks/LJ-1-519/Probe519.agdai` before each run.
Three rechecks each, median reported.

| target | median wall | median peak RSS | runs |
|---|---|---|---|
| W3 alone, obligation omitted | 2.27 s | 401 MB | `runs/w3-1..3` |
| the full file | 2.73 s | 434 MB | `runs/full-1..3` |

W3 alone: 2.27, 2.35, 2.26 s. Full: 3.02, 2.73, 2.53 s.

The probe is 243 lines. The estimate was about 200, of which about 55 was the
obligation. The obligation is not among them. The file carries the D-10
census, W3, the obligation type, two controls, Part A, Part B and the
reduction.

**A raw `.agda` probe carries no ` ```agda ` fence, so the ratio bar's
divisor is 0 and the bar cannot fire on this return.** Nothing here is
funded against `[LJ-1.517]`'s census run.

## 8. WHAT I COULD NOT CLOSE

- `hier-in-stage-limit`. It reduces to `StageHigh`, which needs
  `hierL (sucV γ) ∈ Lset (step 4 γ)`. The tree's only route into a stage is
  `Lset-in` (`src/L/Constructible.lagda.md:319`) through `𝒟ₒ-intro`
  (`src/L/Constructible.lagda.md:301`), which demands a `Formula` over the
  stage. That is stage-level definability of the tower, which this brief
  forbids at `agents/tasks/LJ-1-519/LJ-1.519.md:100`.
- The brief's exact spelling without `IsOrd γ`. Section 6.
- `StageLow`. I state it and do not build it. Devlin's `δ > ω` excludes the
  tail and his text does not cover it, so it is a residue his proof leaves as
  well, and I did not invent a source for it.

## 9. WHAT THE NEXT BRIEF NEEDS

1. **Do not order `hier-in-stage` at a limit again.** The limit's
   contribution is built and it is complete. Ordering it again buys nothing.
2. **The orderable statement is `StageHigh`**, and it has no `α`. Whether it
   is reachable is a question about `[LJ-1.494]`'s NO-GO, not about limits.
3. **The premise "at a limit it is Devlin 2.6(ii)" is true and does not carry
   what the brief took from it.** The source states 2.6(ii) and defers its
   proof to the reader (`_build/literature/dev2.txt:678`). A statement with a
   sourced STATEMENT is not a statement with a sourced ROUTE, and the
   distinction decided this task.
4. **`IsLimit` does not exist in `src/`.** If a future statement in `src/`
   needs it, it must be added, and the two existing spellings
   (`src/L/InjChain.lagda.md:109`, `src/L/SquareLawClosed.lagda.md:125`)
   already fix its shape.
5. **W2 is not engaged by this task.** Nothing here is written at a fixed
   carrier that a generic one would serve; `two-below`, `steps-stay` and
   `stage-below` are generic in `α`, `γ` and `n` already. **W4 is not
   engaged either: no module was retired and nothing was deleted.**

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, and it set the target.**
  `dev/literature/devlin-II5.md:221` reads "live inside L_α; that is 2.6(ii),
  the sequence (L_δ | δ ≤ γ) ∈ L_α for". Also `:218` "2. Uniform Δ₁ at limit
  α > ω (`dev2.txt:674-686`, 2.6-2.7): for γ < α," and `:331` "5. The
  KP-Recursion Theorem 1.11.8: used in 2.6's proof to construct the", which
  is what sent me to the primary text.
- `dev/literature/level-formula-slot-roles.md`: **READ.** Line 24 carries the
  row for Devlin 2.6 and confirms that `G` says `f = (L_γ | γ ≤ α)` with `f`
  and `α` free in the roles SEQUENCE and ORDINAL. This is the outside check
  on reading `seq γ` as `hierL (sucV γ)`.
- `dev/literature/truncation-and-selection.md`: **READ, one section.** Line
  88 reads "## 2. THE TYPE-THEORY SIDE: when a truncation can be
  untruncated". Used only for section 4's remark that W3's truncation is not
  needed.
- `dev/literature/digest.md`: **NOT USED.** It is the rud-route digest
  (`dev/literature/digest.md:1`). This task is the Def tower's level
  sequence, and `dev/literature/devlin-II5.md:24` records that the Def-side engine was
  added by that digest and not by this one. Declined.
- `dev/literature/terms-2026-08.md`: **NOT USED.** It is a terminology
  dossier for a naming ruling (`dev/literature/terms-2026-08.md:1`). No term
  was named or renamed in this task. Declined.
- `dev/literature/devlin-errata.md`: **READ, on the brief's instruction**, at
  `dev/literature/devlin-errata.md:125` "### 2.3 Errors in Chapter II (WS pp.
  62-63)". **The Chapter II list does not reach 2.6.** Its three items are
  amenability at Devlin p. 45, the uniformity claim for `Sat` at p. 65, and a
  claim at p. 66 about Σ₁ over `L_λ`. `dev/literature/devlin-II5.md:30` records the same boundary. **So 2.6(ii) is not on the errata list, and "not on the errata
  list" is not the same as "proved": the gap I report is in the text itself,
  not an error someone else already caught.**
- `_build/literature/dev2.txt`: **READ, and it is the decisive source.**
  Line 678 reads
  "(Ly\y ^ δ)e L δ + 4 , so we are done. (We leave all the details to the reader.) D".

## ARCHIVE USED

`grep -rln "hier-in-stage\|2.6(ii)" archive/` returns NOTHING. All five
candidates are declined, each in writing:

- `archive/dev/LJ-dispatch-index.md`: **NOT READ, declined.** It is a
  dispatch index. The predecessor evidence this task needs is the live
  `[LJ-1.517]` report and probe, which the brief names and I opened.
- `archive/dev/JOURNAL.md`: **NOT READ, declined.** A journal is history, and
  it carries no obligation type or price for this site.
- `archive/dev/JOURNAL-archived.md`: **NOT READ, declined.** Same reason.
- `archive/dev/ORCHESTRATION.md`: **NOT READ, declined.** It is the archived
  operating document. This task's rules came from `dev/pod/instructions/coder.md`,
  `AGENTS.md` and the brief.
- `archive/dev/DECISIONS-archived.md`: **NOT READ, declined.** A bare `D<n>`
  resolves only against this file and no `D<n>` code is in play here. The
  codes this task touched are W2, W3, W4, AD12, D-10, C-22, C-42 and P-l, all
  live.
