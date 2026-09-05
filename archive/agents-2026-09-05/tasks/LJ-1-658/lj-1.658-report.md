# [LJ-1.658] report: is the collapse image inside L

GO. Exit 0. `0 UNRESOLVED of 1` (`agents/tasks/LJ-1-658/runs/witness-final.out:2`).

## 1. THE VERDICT

**`C.πX ⊆ L` is TRUE, and it costs 15 lines.** The obligation is at
`agents/tasks/LJ-1-658/Probe658.agda:282`:

    pix-in-L : (lam : S) (ordλ : IsOrd lam) (succλ : ...) (X : S)
      (X⊆L : ...) (∅∈λ : ...)
      → Site.Cover lam ordλ succλ X X⊆L ∅∈λ
      → Site.Target lam ordλ succλ X X⊆L ∅∈λ

`Site.Target` (`Probe658.agda:150`) is the brief's type,
`(x : S) → ⟨ x ∈ˢ HS.C.πX ⟩ → ⟨ isL x ⟩`.

**IT TAKES ONE HYPOTHESIS, `cover`, AND `cover` IS NOT NEW DEBT.** It is the
SECOND parameter of the chapter's own `module Condense`
(`src/L/BoundedSubset.lagda.md:918-920`), and the chapter's top consumer already
carries it as a hypothesis at `src/L/BoundedSubset.lagda.md:1672-1673`. So fork
(a) adds nothing to the books. It moves a fact that was already owed.

**IT DOES NOT TAKE `levelIn`.** That is the point of the task, and section 3
measures it against the brief's own premise 2.

## 2. AND THE LEG IT WAS FUNDED FOR IS ALSO DISCHARGED

`[LJ-1.653]` funded fork (a) to close `HoodSoundP` leg 2
(`agents/tasks/LJ-1-653/lj-1.653-report.md:1`). **I did not stop at the fork. I
closed the leg**, at `Probe658.agda:317`:

    soundP-leg2-from-pix : ... (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) → Δ₀ φ₀
      → Site.Target ...            -- fork (a)
      → Site.LsetOnlyAt ... φ₀     -- Lset-only at the CLASS carrier
      → Site.HoodSoundP ... φ₀

`Site.HoodSoundP` (`Probe658.agda:226`) is `[LJ-1.653]`'s type verbatim
(`agents/tasks/LJ-1-653/Probe653.agda:235-240`). `Site.LsetOnlyAt`
(`Probe658.agda:219`) is `L.Hierarchy`'s delivered `Lset-only`
(`src/L/Hierarchy.lagda.md:334-335`) read at `w = zero`, `b = suc zero`, over a
pinned parameter-free formula.

**SO LEG 2 NEEDS NOTHING BEYOND FORK (a) AND THE CHAPTER'S OWN LEVEL-HOOD
RESIDUE.** The whole transfer between the two carriers is 25 lines
(`Probe658.agda:212-213` and `:237-271`), and it is four moves:

1. `AbsπX.abs₀`, `[LJ-1.653]`'s leg 1, out of the collapse's inner reading into
   the ambient one. Free, as 653 measured (`Probe658.agda:258-259`).
2. `⊨-map` along the carrier map (`src/FOL/Manipulation/Relabelling.lagda.md:154`),
   plus the parameter-free fixpoint. The ambient reading does not see which
   constant domain carries it (`Probe658.agda:262-267`).
3. `AbsL.abs₀` backwards, into the class carrier's own reading
   (`Probe658.agda:269-270`).
4. `Lset-only` reads the value off.

**THE CARRIER MAP IS FORK (a) AND NOTHING ELSE.** `toL` (`Probe658.agda:212`)
takes `Site.Target` and not `Cover`, on purpose: its type is
`CIso.I.SPM → AbsL.SM`, so inhabiting it IS producing `⟨ isL x ⟩` from
`⟨ x ∈ˢ C.πX ⟩`. Nothing weaker inhabits it. The `Cover` form
(`Probe658.agda:273`) is the composite and is one line.

**THIS CLOSES FORK (b) AS A REQUIREMENT.** `[LJ-1.653]` named the alternative:
an ambient form of `Lset-only`, the deleted Crossing section, priced as a
GCH-trophy rebuild (`dev/ARCHIVE.md:285`, `dev/ledger.toml:1021-1026`). **Fork
(b) is not needed for this leg.** The class-carrier `Lset-only` already in the
tree is enough once fork (a) supplies the carrier map. Fork (b) may still be owed
by other consumers; this task measures only that leg 2 does not need it.

## 3. THE BRIEF'S PREMISE 2 IS REAL, AND IT IS NOT USABLE HERE

Premise 4 asked whether premise 2 is in scope at the site. **It is in scope, and
that is not the problem. The problem is what reaching it costs.**

`πX⊆Lβ` (`src/L/BoundedSubset.lagda.md:997`) sits inside `module Condense`, whose
FIRST parameter is `levelIn` (`src/L/BoundedSubset.lagda.md:917`). Agda gives no
term of a parameterised module without its parameters. So premise 2's route
carries `levelIn`, which is the fact fork (a) was funded to close.

**I MEASURED THIS RATHER THAN ASSERTING IT.** `pix-in-L-via-premise2`
(`Probe658.agda:178`) reaches the same target through premise 2, in 7 lines, and
it typechecks:

    pix-in-L-via-premise2 : LevelIn → Cover → Target
    pix-in-L-via-premise2 li cov x x∈πX =
      Lset→isL Cd.β Cd.β-isOrd x (Cd.πX⊆Lβ x x∈πX)
      where
      module Cd = HS.Condense li cov

Set it beside `pix-in-L-at` (`Probe658.agda:159`), which takes `Cover` only. The
difference between the two signatures is the finding.

**AND THE `src/` DEFECT IS SEPARABLE, WHICH IS THE PART THE NEXT BRIEF CAN
ACT ON.** The BODY of `πX⊆Lβ` never mentions `levelIn`. It uses `C.πX-member`,
`cover`, `ord∈β` and `Lset-mono` only (`src/L/BoundedSubset.lagda.md:997-1008`),
and the `β` block above it is hypothesis-free
(`src/L/BoundedSubset.lagda.md:925-954`). Only three terms of `Condense` use
`levelIn`: `β-succ` through `sucV∈β`, and `Lβ⊆πX`
(`src/L/BoundedSubset.lagda.md:1020`). **So `Condense` is two modules wearing one
telescope**, and a split that puts `β`, `β-isOrd` and `πX⊆Lβ` under `cover`
alone would make premise 2 usable as premise 2 was written. I did not make that
change: nothing lands in `src/` from this task.

## 4. W3, THE WIDEST UNMEASURED TERM

The brief named it: reaching `Lset→isL` from `x ∈ˢ Lset β`, estimated at 40 to
100 lines on the basis that `[LJ-1.655]` had to transport `elem` across a module
boundary (`agents/tasks/LJ-1-655/lj-1.655-report.md:1`).

**MEASURED: THE TRANSPORT IS ZERO LINES, AND THE ROUTE THE ESTIMATE PRICED IS
NOT THE ROUTE THAT CLOSES.**

- There is no transport, because there is no module boundary to cross. `Lset→isL`
  is a top-level function of `L.Constructible`
  (`src/L/Constructible.lagda.md:405-406`) and is imported directly.
- There is no `β` either. The estimate assumed the route runs
  `x ∈ˢ C.πX → x ∈ˢ Lset β → isL x`. **The route that closes never builds `β`**:
  `cover` hands back an ordinal `γ` with `C.π y ∈ˢ Lset γ` already, so
  `Lset→isL γ oγ` applies at once (`Probe658.agda:121-126`). The `β` supremum is
  a detour.
- **The measured decisive miniature is 15 non-blank non-comment lines**, over
  four rows: `πX⊆L` (`Probe658.agda:108-113`), `cover→coverL`
  (`Probe658.agda:121-126`), `πX⊆L-from-cover` (`Probe658.agda:128-129`) and the
  instance `pix-in-L-at` (`Probe658.agda:159-160`). **The estimate is high by
  about a factor of three at the low end and seven at the high end.**

The delivered file is 145 non-blank non-comment lines over 325. The extra is
section 2's leg-2 bridge (25 lines), section 3's contrast (7 lines), the type
declarations, and the two telescopes.

## 5. W2, THE GENERIC CARRIER

Answered, and it is the reason section 4's number is what it is.

**The mathematics is written ONCE, at an arbitrary set.** `module Coll (M : S)`
(`Probe658.agda:85`) takes a bare `S`: no hull, no stage, no extensionality, no
ordinal, and it does not import `L.BoundedSubset` or `L.Hull` at all. `πX⊆L`
(`Probe658.agda:108`) is proved there.

**Every later row is an instance and not a second proof.** `module Site`
(`Probe658.agda:136`) instantiates it at the chapter's own telescope
(`src/L/BoundedSubset.lagda.md:903-905`) and the body of the obligation is
`K.πX⊆L-from-cover cov` and nothing else (`Probe658.agda:160`). `Coll HS.M`'s
`C` and `HullStage`'s `C` are the same `Collapse HS.M`, so no adapter stands
between them. **That is what made the transport zero.**

`Coll` also states the weakest sufficient hypothesis separately from the
chapter's own. `CoverL` (`Probe658.agda:92`) asks only that each collapse VALUE
is constructible; `Cover` (`Probe658.agda:97`) is the chapter's, and
`cover→coverL` (`Probe658.agda:121`) discards two of its three components. So a
future consumer that cannot supply the full `cover` has a smaller target named
and proved sufficient.

I did not meet a conflict between W2 and a deadline.

## 6. THE LAWS IN THE BUNDLE

- **D-10** (`dev/LESSONS.md:1375`), price the truth before the proof. Done
  first, and it is section 3: the recorded route (premise 2) is TRUE and the
  target is TRUE, but the recorded route carries a hypothesis that makes it
  useless for the purpose. The corrected route is recorded beside it, both green
  in one file.
- **P-l** (`dev/LESSONS.md:2367`). No statement in this file names a transparent
  presentation. `HS.M`, `HS.C.πX` and `Lset` enter the types as atoms, and the
  one concrete environment is the two-entry vector at `Probe658.agda:245`, which
  is a vector of the statement's own bound variables and not a stage value.
- **C-42** (`dev/LESSONS.md:3762`). No refutation landed, so no sweep is owed.
- **D-26** (`dev/LESSONS.md:1735`) and **C-22** (`dev/LESSONS.md:2307`) did not
  bind. No well-founded key was built, and the deliverable is a probe, written
  and checked in five increments (`runs/floor-0` to `runs/final-3`), not at the
  end.

## 7. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the program and
untouched here. One Agda process at a time. All runs from the repository root.
`agda -i src -i agents/tasks`.

**FLOOR FIRST, AND IN TWO STEPS, because the frame has two halves.**

| run | what | wall s | peak RSS bytes | exit |
|---|---|---|---|---|
| `runs/floor-0` | generic frame, NO `L.BoundedSubset` | 1.27 | 270,303,232 | 0 |
| `runs/floor-1` | frame plus the `HullStage` telescope | 3.12 | 742,866,944 | 0 |

**Reaching the site is 1.85 s of the 3.12 s floor and about 470 MB of the peak.**
The generic core of section 5 costs a quarter of that, and it is where the
mathematics is.

Three forced rechecks of the delivered file, each with the probe's interface
deleted first:

| run | wall s | peak RSS bytes | exit |
|---|---|---|---|
| `runs/final-1.out` / `.time` | 2.78 | 730,316,800 | 0 |
| `runs/final-2.out` / `.time` | 2.95 | 730,316,800 | 0 |
| `runs/final-3.out` / `.time` | 2.71 | 730,316,800 | 0 |

Median wall **2.78 s**. Peak RSS **730,316,800 bytes** on all three. Each printed
`Checking`. No heap event, and no restructuring was needed.

**THE TERMS ARE NOT SEPARABLE FROM THE FRAME AT THIS CALIBER.** The floor
measured 3.12 s in one run and the delivered file rechecks at a median of 2.78 s
over three. The two brackets overlap, so **this object is frame-bound and the
proof content is below the noise.** I report the overlap rather than a
difference, because a difference here would not be a measurement.

Earlier kept runs, not among the three: `runs/p-0` (3.62 s, 608,403,456 bytes,
exit 0, PARTS 1 to 4, the obligation alone); `runs/p-1` (exit 42, one
`[UnequalLevel]` at `Probe658.agda:262`, a transport DIRECTION slip and not a
mathematical one: the composite path ran from the class carrier to the collapse
carrier and the `subst` needed the other end. The fix is one `sym`);
`runs/p-2` (3.67 s, exit 0, the fix); `runs/p-3` (4.22 s, exit 0, after the
bridge was refactored to take `Target` in place of `Cover`);
`runs/final-confirm` (4.16 s, 754,319,360 bytes, exit 0, the delivered file
after five in-file comment citations were corrected against
`agents/tasks/LJ-1-653/Probe653.agda`; code unchanged).

Witness meter, one obligation: `runs/witness-final.out`, `pass exit=0 3.12s`,
`0 UNRESOLVED of 1`, `probe_red=False`. This worktree has no `.venv`; the meter
ran as `/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`. I
did not add a dependency and I did not create a local `.venv`.

**THE RATIO BAR CANNOT FIRE ON THIS RETURN.** The write scope holds no
`.lagda.md` and no ` ```agda ` fence, so the in-fence divisor is 0. Nothing
landed in `src/`.

## 8. WHAT THE NEXT BRIEF NEEDS

1. **FORK (a) IS CLOSED AND LEG 2 IS CLOSED WITH IT. Do not fund either
   again.** Both are green at `Probe658.agda:282` and `:317`.
2. **THE CAMPAIGN'S REMAINING RESIDUE ON THIS ROUTE IS THE LEVEL-HOOD FORMULA
   ITSELF, AND IT IS THE CHAPTER'S OWN.** `soundP-leg2-from-pix` is generic in
   `φ₀`. To use it, somebody must pin `φ₀`, supply `Δ₀ φ₀`, and supply
   `LsetOnlyAt φ₀`. That is the chapter's named residue
   (`src/L/BoundedSubset.lagda.md:901-902`), not new debt. The next brief should
   pin `φ₀` at the chapter's `LevelHood0` shape
   (`src/L/BoundedSubset.lagda.md:840-859`) and ask whether
   `L.Hierarchy`'s `Lset-only` (`src/L/Hierarchy.lagda.md:334-335`) instantiates
   at it. **That is one dispatch, and it is the last one before `levelIn`
   falls**, because `[LJ-1.653]`'s `levelin-from-hood-pf`
   (`agents/tasks/LJ-1-653/Probe653.agda:289`) then takes `HoodSoundP` and
   `HoodExistsP` and returns `LevelIn`.
3. **`cover` BECOMES THE ONE SURVIVING HYPOTHESIS OF `Condense`.** With leg 2
   closed and `HoodExistsP` supplied, `levelIn` is derived, so
   `src/L/BoundedSubset.lagda.md:1671-1673` goes from two hypotheses to one.
   `archive/dev/LJ-dispatch-index.md:236` predicted this shape and this task is
   the first term that carries it.
4. **A `src/` SPLIT OF `module Condense` IS AVAILABLE AND CHEAP.** Section 3
   names the exact three terms that use `levelIn`. A split would let a future
   consumer use `β` and `πX⊆Lβ` without it. This is a refactor and not
   mathematics; it needs its own task and it changes no statement.
5. **`HoodExistsP` IS STILL UNBUILT.** Nothing in this task touches it.
6. **`PiReflectsOrd` IS STILL UNBUILT** and `[LJ-1.653]` section 9 item 3 still
   stands.
7. This task changed nothing in `src/`.

## 9. GATES

Run individually while the work was live, as the Boundary requires:

- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10031 tracked
  files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.

The probe interface was deleted after the last run, so the working tree carries
no generated file. I did not run `make check`. I did not commit and I did not
push.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ.**
  `archive/dev/LJ-dispatch-index.md:236` reads
  `| LJ-1.160 | Read the 845-line level substrate against levelIn and cover | THE WALL IS BYPASSED, 16 LINES | Both hypotheses from one crossing face at the collapse image. The wall term is absent |`.
  **That row is this task's shape, written down before the term existed**: both
  hypotheses fall out of one fact at the collapse image. Section 8 item 3 is the
  same claim with a green term under it. `archive/dev/LJ-dispatch-index.md:222`
  carries the price the wall was booked at, "About 1.0k lines", which section 4
  measures at 15 for fork (a) and 25 for the bridge.
- **`archive/dev/DECISIONS-archived.md` READ.**
  `archive/dev/DECISIONS-archived.md:52` is D32, and it reads in part
  `Arm B is severed by deletion; the internalization rebuild is deferred to the GCH resume, comprehensively documented`.
  This is fork (b)'s row. It is why section 2 states explicitly that leg 2 does
  NOT need the rebuild: the deleted content is a GCH-resume item and this leg
  now closes without it.
- **`archive/dev/JOURNAL-archived.md` READ.**
  `archive/dev/JOURNAL-archived.md:2507` reads
  `The check time falls 150.2 s to 11.5 s. `ambientOnly-from` carried 92`.
  That is the measured cost of the ambient form of `Lset-only`, the fork (b)
  route. Set against section 7's median of 2.78 s for the whole delivered file,
  it is the reason fork (a) was the right fork to fund.
- **`archive/dev/JOURNAL.md` DECLINED.** Surveyed by grep, not read. Its four
  hits for `collapse` (`:412`, `:417`, `:471`, `:645`) are about a step
  collapsing to `⊤̇` and about counting, not about the Mostowski collapse image.
  Nothing on this route.
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read. It is the archived
  process document and carries no mathematics: zero hits for `collapse`.
- **`dev/ARCHIVE.md` READ**, although the search did not name it.
  `dev/ARCHIVE.md:285` carries the Crossing partial-cut row and reads in part
  `The Crossing section stated the ambient-reading form of `Lset-only` at the class carrier.`
  It is fork (b)'s revival condition, and section 2 measures that this leg does
  not trigger it.

## LITERATURE USED

- **`dev/literature/devlin-II5.md` READ.** `dev/literature/devlin-II5.md:96`
  reads `> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]` and
  `dev/literature/devlin-II5.md:99` reads
  `> (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)].`
  **These are the two readings section 2's bridge moves between**: (a) is the
  unrelativized reading, which is where `Lset-only` stands at the class carrier,
  and (b) is the relativized one, which is where `HoodSoundP` stands at the
  collapse. Devlin joins them by 1.9.15; the tree joins them by two `abs₀`
  applications and one relabelling. The source confirms the route and does not
  confirm the price.
- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | `Φ(z,v,γ)` with `∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]` | 3 in `Φ`, ONE closed | `z` at position 0 | `v` at 1, `γ` at 2 | **VALUE, ORDINAL** | `_build/literature/dev2.txt:1186-1191` |`.
  **I used it to fix the slot arithmetic of `LsetOnlyAt`** (`Probe658.agda:219`),
  which reads the VALUE at slot `zero` and the ORDINAL at slot `suc zero` over
  arity 2, with `z` bound inside. That matches row 4 once `z` is existentially
  closed, which is what `GraphAt w b = ∃̇ (...)` does
  (`src/L/Coding/Sequence.lagda.md:292`). Without this file the two free slots
  could have been numbered the other way and the term would have been wrong in a
  way that still typechecks against a symmetric hypothesis.
- **`dev/literature/digest.md` DECLINED.** Surveyed by grep, not read. It is the
  whole-book index, and `devlin-II5.md:18` already names the section of it that
  applies. Its one on-route hit, `:345`, is the argument shape at the book level
  and adds nothing to a carrier map.
- **`dev/literature/truncation-and-selection.md` DECLINED.** Not used. This task
  took no truncated choice and selected no code. Its two matches (`:241`, `:264`)
  are about other formalizations of L, not about this transfer.
- **`dev/literature/geology.md` DECLINED.** Not used. Set-theoretic geology is
  not on this route, and its `absolute` hits (`:409`, `:504`, `:508`) are about
  absoluteness between GROUND MODELS, which is a different question from
  absoluteness between two carriers of one model.
