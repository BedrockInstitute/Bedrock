# LJ-1.572 report: `Def` for B9's `g`, from the code the leg already assembled

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO

## VERDICT

**NO-GO, AND THE REASON IS NOT THE ARITY.** The brief names the arity as "the
whole risk in this task". THE ARITY IS FREE. The three formula conjuncts are
arity-polymorphic and come to 3 with no work at all. That is measured, not
argued, at `agents/tasks/LJ-1-572/Probe572.agda` section 1.

**THE REASON IS THE FRAME, AND IT MISSES ON BOTH COMPONENTS.** `[LJ-1.566]`'s
`injcode-assembled` is at an `a` that must be an ORDINAL, and at a `b` the
carve PRODUCES. B9's `a` is `Lset δ`, a stage and not an ordinal, and B9's `b`
is `δ`, GIVEN. The brief says a named frame mismatch is a full result. It is
named below, and the attempt to put it to the elaborator ran away: that is the
sharpest number this task produced.

**AND UNDER THE FRAME THERE IS A SECOND REASON THAT SURVIVES ANY REPAIR OF
IT.** `InjCode` at B9's pair IS B9's obligation, because
`InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:37-38`). So
`InjCode` at that pair is what `Def` BUYS, not what buys `Def`. The brief's
central premise inverts the dependency.

**WHAT IS DELIVERED.** Three files that typecheck and one that does not, and
the one that does not is itself the measurement. No hole and no postulate in
any of them, nothing in `src/`, no commit and no push:

| file | lines | cold | warm | exit |
|---|---|---|---|---|
| `agents/tasks/LJ-1-572/Probe572.agda` | 349 | 492.71 s, 1.89 GB (`runs/probe-3.out`) | 3.06 s (`runs/probe-4.out`) | 0, 0 |
| `agents/tasks/LJ-1-572/runs/W3.agda` | 112 | 421.37 s, 1.40 GB (`runs/w3-2.out`) | 1.57 s (`runs/w3-3.out`) | 0, 0 |
| `agents/tasks/LJ-1-572/runs/Frame2.agda` | 140 | not run cold | 1.83 s (`runs/frame2-1.out`) | 0 |
| `agents/tasks/LJ-1-572/runs/Frame.agda` | 149 | **1360.52 s, KILLED** (`runs/frame-1.out`) | **>300 s, KILLED** (`runs/frame-2.out`) | 143, killed |

`runs/probe-1.out` (530.07 s) and `runs/probe-2.out` (3.53 s) are the same
file with one term named `obligation-is-row-4`. I renamed it to
`obligation-pays-B9` because the first name claimed more than the term proves:
it buys B9 at its CORRECTED target, not row 4 as `[LJ-1.564]` states it. Four
green runs of the probe in all, exit 0 every time.

Caliber `-A64m -I0 -M8g`, taken from the pane. I did not set `GHCRTS`. One Agda
process at a time. **No run gave exit 251 and no run hit a heap wall.**

Gates run individually and all clean: `lint-agda.py --check`,
`check-probes.py --check`, `lint-prose.py --check`, each exit 0.
`git status --porcelain` shows one untracked path, `agents/tasks/LJ-1-572/`.
Nothing in `src/`. No commit and no push.

**WHAT IS NOT DELIVERED.** `Probe572.agda` binds no term named
`b9-g-is-definable`. The obligation stands open. `review-of-b9-g-definable.md`
is the stop.

**AND THE OBSTRUCTION IS NOT THE FORMULAS AT ALL.** W3 unfolded B9's `g` and
found it is built through `sq`, a bare module parameter
(`src/L/StageCardinal.lagda.md:17-19`). `Probe572.agda` `sq-is-SqFam` then
checks that `sq` IS `SqFam α₀` (`src/L/StageBound.lagda.md:36-40`), whose
producer the chapter itself marks **"Not inhabited"** (`:42`). **The coding
leg's formulas answer the question they were built for. They were built about a
CODE, and B9 has no code until something gives its `g` a formula.**

**I STATE THE LIMIT OF THIS EXACTLY.** I did NOT prove `Def` false at B9's `g`,
and I could not: a definable `sq` would make it true. What is measured is that
the obligation's truth is a function of a parameter the module quantifies over,
and that the tree gives that parameter no formula.

## THE FORMULA AND ITS ARITY

**THE BRIEF ORDERS THIS SECTION AND IT ORDERS THE ARITY READ FIRST. THE ARITY
IS FREE, AND THE BRIEF'S SENTENCE "that is the whole risk in this task" IS
WRONG.**

**WHAT `Def` WANTS.** A `Formula S 3`. `Def a b g` is `P554.LinkAt a (val a b g)`
(`agents/tasks/LJ-1-568/Probe568.agda:189-190`), and `LinkAt`'s Σ is over
`Formula S 3` (`agents/tasks/LJ-1-554/Probe554.agda:81-82`).

**WHAT `InjCode` HAS, AND AT WHAT ARITY.**

| conjunct | signature | home | used at |
|---|---|---|---|
| `svAt` | `∀ {n} → Fin n → Formula S n` | `src/L/Coding/Model.lagda.md:210` | `Formula S 2`, `src/L/Cardinal.lagda.md:225` |
| `domAt` | `∀ {n} → Fin n → Fin n → Formula S n` | `src/L/Coding/Model.lagda.md:278` | `Formula S 2`, `:226` |
| `injAt` | `∀ {n} → Fin n → Formula S n` | `src/L/Coding/Injection.lagda.md:44` | `Formula S 2`, `:227` |

**ALL THREE ARE ARITY-POLYMORPHIC, SO ALL THREE COME TO 3 AT NO COST.**
`Probe572.agda` section 1 typechecks `svAt₃`, `domAt₃` and `injAt₃`, each
ascribed at `Formula S 3`. **I had to change nothing to get them there.**

**WHAT I USED, AND IT IS NOT ONE OF THEM.** I used NO conjunct of `InjCode` in
any row of the obligation's neighbourhood, because none of them can appear
there. The reason is section 2 of the probe and it is the answer to the brief's
other D-10 question:

**`Def` WANTS BOTH DIRECTIONS AND `InjCode` GIVES NEITHER.** Both halves of
`Def` mention `g` (`agents/tasks/LJ-1-554/Probe554.agda:83-86`). `InjCode` has
type `S → S → S → Type (ℓ-suc ℓ)` (`src/L/Cardinal.lagda.md:223`): it takes
three SETS and no function. `injcode-names-no-function` in the probe is that
ascription. **A type that never mentions `g` cannot state a direction of a link
to `g`.**

The difference is in where the code sits. `svAt`, `domAt` and `injAt` are
evaluated at the environment `(F ∷ a ∷ [])`, with the code `F` IN the
environment: they are statements ABOUT a code. `Def`'s formula is evaluated at
`(y ∷ x ∷ z ∷ [])` with no code in the environment at all. **The assembled
formulas describe a code you already have. `Def` is what gets you one.**

The one bridge the tree holds between a code and `Def` runs FROM a graph L-set
TO `Def`: `graph→def` (`agents/tasks/LJ-1-568/Probe568.agda:368-371`),
re-ascribed as `graph-gives-def`. A graph L-set is `W`'s conclusion
(`agents/tasks/LJ-1-561/Probe561.agda:160-163`). **There is no row running the
other way, and section 2 of the probe says why there cannot be one.**

## WHAT THIS DOES TO THE BILL

`[LJ-1.564]`'s bill is five rows, `gch-from-five`
(`agents/tasks/LJ-1-564/Probe564.agda:456-464`).

| row | term | this task |
|---|---|---|
| 1 | `P550.AmbientCardAtSucc` | **NOT PAID. NOT ATTEMPTED.** |
| 2 | `P550.SqAt` | **NOT PAID. NOT ATTEMPTED. AND IT IS THE OBSTRUCTION, see below.** |
| 3 | `P550.CoHyps` | **NOT PAID. NOT ATTEMPTED.** |
| 4 | `StageCountedCoded` | **NOT PAID.** The obligation is not inhabited. |
| 5 | `P558.SuccIntoPower zf` | **NOT PAID. NOT ATTEMPTED.** |

**THIS TASK PAYS NO ROW. I INHABITED NOTHING THAT DISCHARGES ANY OF THE FIVE.**
`[LJ-1.571]` set that standard this hour and I keep it.

**AND ROW 4 IS NOT WHAT A GO WOULD HAVE PAID EITHER. THE BRIEF SAYS "A GO PAYS
ROW 4 OF FIVE" AND THAT IS TOO STRONG.** Row 4 is
`StageCountedCoded = (δ Lδ : S) → IsOrd (fst δ) → (fst Lδ ≡ Lset (fst δ)) → InjL Lδ δ`
(`agents/tasks/LJ-1-564/Probe564.agda:127-130`). **It carries NO side condition
on δ.** `[LJ-1.561]`'s `w→B9` concludes at a δ that is in `sucV α₀` and outside
`ω` (`agents/tasks/LJ-1-561/Probe561.agda:376-381`), because
`[LJ-1.533]` refuted the unrestricted form
(`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md:22-52`, cited at
`Probe561.agda:372-375`). **So the obligation, inhabited, buys B9 at its
CORRECTED target and not row 4 as the bill states it.** A next brief must not
carry the brief's sentence forward.

**WHAT THE OBLIGATION IS WORTH, MEASURED.** `obligation-pays-B9` in the probe
takes the obligation as a hypothesis and returns
`InjL (LsetS δ oδ) (ordS δ oδ)`, through `[LJ-1.568]`'s
`restrict→B9 Def∥ def∥-restricted` (`Probe568.agda:285-291`). `[LJ-1.568]`
proved that at a QUANTIFIED `H` (`no-free-lunch-at-B9`,
`Probe568.agda:454-463`). The probe's row puts it at THIS brief's own
hypothesis and at B9's own `g`.

**READ IT AS A PRICE. THE OBLIGATION IS NOT A STEP TOWARD THE B9 SITE. IT IS
THE B9 SITE.** The brief estimates it at about 40 lines of a 170-line probe.

**AND ROW 2 IS WHERE THE OBSTRUCTION ACTUALLY LIVES.** `Probe572.agda`
`sq-is-SqFam` checks that `L.StageCardinal`'s `sq` parameter IS `SqFam α₀`
(`src/L/StageBound.lagda.md:36-40`). `SqFam`'s producer is `SqCollect`, and the
chapter's own comment above it says **"Not inhabited"**
(`src/L/StageBound.lagda.md:42`). `[LJ-1.550]` records the same at R2
(`agents/tasks/LJ-1-550/Probe550.agda:304-311`), and R2 is `P550.SqAt`, row 2 of
this bill.

**SO ROW 4's `g` IS BUILT OUT OF ROW 2's OWN OBJECT.** That is the sentence a
next brief needs, and it is the reason this task could not be paid by any
repair of the formulas: the formulas were never the missing part.

## W3, THE WIDEST UNMEASURED TERM

**GREEN, EXIT 0. COLD 421.37 s, WARM 1.57 s.**
`agents/tasks/LJ-1-572/runs/W3.agda`, 112 lines. `runs/w3-2.out` is the first
green run and `runs/w3-3.out` is the same file later in the session.
`runs/w3-1.out` is the first attempt, exit 42, and it is kept because it is a
measurement: the bare pair `(δ , isL-ord δ oδ)` blocks on a meta outside an
application, and `[LJ-1.568]` had already named `ordS` for exactly that reason
(`agents/tasks/LJ-1-568/Probe568.agda:100-101`). I re-named it and the file
went green.

**THE BRIEF ESTIMATED "about 12 lines, under 60 seconds". THE LINE COUNT WAS
RIGHT AND THE TIME NEEDS BOTH NUMBERS TO BE READ HONESTLY.** The first green
run took 421.37 s. **THAT WAS NOT THE UNFOLDING.** The identical file re-runs
in 1.57 s, against `[LJ-1.568]`'s W3 at 1.46 s
(`agents/tasks/LJ-1-568/lj-1.568-report.md:192-193`). **The 421.37 s was
one-time interface work in a fresh worktree, and the unfolding itself is
cheap.** I first read that number as the cost of the `refl` hops. The warm
re-run refutes that reading, and the corrected reading is the one to carry
forward: **asking `stage-card-upper`'s body to unfold costs about a second.**

**WHAT IT MEASURED.** Three rows, each one a `refl` or an ascription, so the
chain is checked and not quoted:

| hop | row | what it fixes |
|---|---|---|
| 1 | `unfold-1`, `runs/W3.agda:90-91` | `stage-card-upper` IS `∈-induction step` |
| 2 | `unfold-2`, `runs/W3.agda:94-98` | `step`'s body is `limit-step` at the branch family |
| 3 | `sq-bare`, `runs/W3.agda:109-112` | `sq` is a BARE parameter: injectivity and nothing else |

**AND HOP 3 IS THE ANSWER TO THE QUESTION THE BRIEF ASKED.** `limit-step`
counts the formulas of every earlier stage into `α`, and its counting bound is
`Bound α oα infα (sq α α∈suc infα)` (`src/L/StageCardinal.lagda.md:283`, used
at `:287-292`). So every value of B9's `g` is a value of `sq`. **`sq` carries
no formula, no `isL`, no stage and no grade.** `[LJ-1.568]` recorded that
sentence (`agents/tasks/LJ-1-568/lj-1.568-report.md:132`). This W3 checks the
two hops between `stage-card-upper` and it, and `Probe572.agda` `sq-is-SqFam`
then names what `sq` is.

## THE RUNAWAY, AND IT IS THE SHARPEST NUMBER THIS TASK PRODUCED

**YOU CANNOT ASK THE ELABORATOR WHETHER `[LJ-1.566]`'s CARVE APPLIES AT B9's
`a`. THE APPLICATION DOES NOT ELABORATE.**

`runs/Frame.agda` is the frame slice with `IsOrd (fst (LsetS δ oδ))` taken as a
PREMISE, and `injcode-assembled` then APPLIED at B9's `a` (`p566-at-B9-a` and
`p566-at-B9-b`). `runs/Frame2.agda` is the SAME FILE with those two
applications removed and `B9-a-carrier` in their place.

| file | interfaces | result |
|---|---|---|
| `runs/Frame.agda` | cold | 1360.52 s, killed, exit 143 (`runs/frame-1.out`) |
| `runs/Frame2.agda` | warm | **1.83 s, exit 0** (`runs/frame2-1.out`) |
| `runs/Frame.agda` | warm | **past 300 s, killed** (`runs/frame-2.out`) |

**THE WARM PAIR IS THE ATTRIBUTION AND IT IS CLEAN.** Same interfaces, same
file, and the only difference is the two applications: 1.83 s against a kill at
300 s.

**IT WAS NOT A HEAP WALL.** On the cold run, RSS was static at 2,314,080 KB
against a `-M8g` cap and CPU time equalled elapsed time (21:36.56 CPU in 21:36
elapsed), so the process held one core and allocated nothing. That is a runaway
elaboration. `runs/frame-1.out` carries the note.

**IT WAS NOT CONTENTION EITHER, AND I CHECKED.** The pane is `machine: shared`
and three other Agda processes were live at the time, two of them at about
8.9 GB RSS (`runs/contention-1.out`). CPU time equal to elapsed time rules that
out as the cause: my process was never descheduled.

**WHY IT MATTERS TO THE NEXT BRIEF.** This is stronger than the frame mismatch
alone. Not only is `IsOrd (Lset δ)` unsupplied; the instance that would consume
it does not reduce. `Carve` runs on `P521.OrdSWO∈ₛ.w (fst a) oa`
(`agents/tasks/LJ-1-566/Probe566.agda:129-130`), the ordinal well-order of the
carrier, and at a carrier that is not an ordinal the carve has nothing to
reduce against. **Do not send a task to repair this by supplying the premise.
The premise is not the problem.**

## ARCHIVE USED

Five CANDIDATE paths. **Three read, two declined.**

**READ.** `archive/dev/LJ-dispatch-index.md:379`:

> `| LJ-1.324 | Transplant stage-card-upper | REFUTED, THE FIRST INGREDIENT IS THE GOAL. DD25 review not needed: it closes a lead and funds nothing | The generic engine survives, tower-blind |`

**THIS IS THIS TASK'S SHAPE, ALREADY REFUTED ONCE.** `[LJ-1.324]` went at
`stage-card-upper` and the refutation was that the first ingredient IS the
goal. The bill section below measures the same circle at `InjCode`. Two rows
further, `:381`:

> `| LJ-1.326 | The miniature that gates BOTH new debts | BUILDS, 14 LINES, AND THE ADAPTER IS 8 | Debt 1's adapter is MEASURED at absorbs' own site, so its 800 is refuted. The gap is a missing FORMULA |`

and one row before, `:378`:

> `| LJ-1.321 | The door: a 2-Constant map Wat to sq | NARROWED. THE DEBT IS ONE PAIRING FUNCTION | A well-order on sq gives the map outright and pullOrder reduces it. The naive map is refuted |`

**`sq` IS A RECORDED, OPEN DEBT AND NOT A DISCOVERY OF THIS TASK.**
`[LJ-1.321]` named it "ONE PAIRING FUNCTION" and `[LJ-1.326]` named the gap "a
missing FORMULA". This task's obligation runs into both.

**READ.** `archive/dev/DECISIONS-archived.md:51` holds the general form of the
obstruction, inside D31:

> `the object language's quantifiers range over sets and not over the host-level formula index family`

That is why an ambient function has no formula unless something in the tree
gives it one. It is stated there about `defSet`. **I do not transfer it by
analogy** (`AGENTS.md:45`). The rows I rely on are measured at their own site
in `Probe572.agda`, and this line is context.

**READ.** `archive/dev/JOURNAL.md:668`:

```
template content bought once. `[LJ-0.7]` found the definable well-order appears
```

The sentence completes at `:669` with "on the whole GCH chain at exactly ONE
place, Devlin's own proof of the hull". It agrees with `[LJ-1.568]`'s pointer
and with the literature below: the definable well-order is the object that
carries a formula, and `sq` is not it.

**DECLINED.** `archive/dev/JOURNAL-archived.md`: not read. A `grep` for
`stage-card-upper`, `LJ-1.533`, `B9` and `InjCode` returned no hit in it, so it
holds no row about this site.

**DECLINED.** `dev/ARCHIVE.md`: surveyed, not used. It is the retired-module
registry ("The registry of Bedrock's retired modules", `dev/ARCHIVE.md:3`), and
this task retires no module and reads none. The same four greps returned no hit
in it.

## LITERATURE USED

Five CANDIDATE paths. **One read, four declined.**

**READ.** `dev/literature/devlin-II5.md:259`:

> `Requirement: a definable well-order of L_α, used to pick the <_L-least`

The paragraph runs to `:266` and the strength line is `:268-270`. **THIS IS THE
OBJECT THAT CARRIES A FORMULA, AND IT IS NOT `stage-card-upper`'s `g`.** The
classical route does not use an arbitrary ambient injection at this site: it
picks the `<ʟ`-least witness of a definable well-order, and that map's graph
carries a formula by construction. `[LJ-1.568]` pointed at exactly this
(`agents/tasks/LJ-1-568/Probe568.agda:485-489`). It is the address for the
next brief, and it is NOT this task's obligation, so I did not build it. AD12
gives this brief one obligation.

**DECLINED.** `dev/literature/truncation-and-selection.md`: not used. It is
about how a proof takes an object out of `∥ A ∥₁` (`:5-9`). This task never
reaches a selection: it stops on the frame, and the truncation `Def∥` carries
is already settled by `[LJ-1.568]` section 4.3.

**DECLINED.** `dev/literature/digest.md`: not used. It pins "the orthodox form
of the rud route" (`:1`). This site is the `defSet` tower, not the rud tower.

**DECLINED.** `dev/literature/terms-2026-08.md`: not used. It is a terminology
dossier for a naming ruling (`:3-4`). This task names nothing new.

**DECLINED.** `dev/literature/geology.md`: not used. It is the set-theoretic
geology dossier for `[L6]` (`:5-8`), a campaign that opens after the trophies
land.

## THE TWO FACTS, RE-VERIFIED

Re-verification ordered by the rewritten brief of 2026-08-23, which parks no
new probe and closes the row on `stop-stated`. Both facts were read at their
own sites in this dispatch, and the chain was re-checked by re-running the
salvaged `runs/W3.agda` (not rebuilt).

1. **`sq` is still a bare parameter with no formula. HOLDS.**
   `src/L/StageCardinal.lagda.md:17-19`. The module header of
   `L.StageCardinal` quantifies
   `sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ →
   (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥) →
   Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
   ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)`. It carries an injectivity
   and nothing else: no `Formula`, no `isL`, no stage, no grade. Read 2026-08-23
   at this dispatch; the line numbers are the ones the original report and
   review cited, and they were right.
2. **`step` still reaches it by the chain the predecessor checked by
   `refl`. HOLDS.** `stage-card-upper = ∈-induction step`
   (`src/L/StageCardinal.lagda.md:566`); `step α IH oα α∈suc infα =
   limit-step α α∈suc oα infα (branch α oα α∈suc infα IH)` (`:562`); the
   `LimitStep` counting bound is `module B = Bound α oα infα
   (sq α α∈suc infα)` (`:283`), consumed by `cnt` (`:288`) and `cnt-inj`
   (`:291`). Re-check: `agents/tasks/LJ-1-572/runs/W3.agda` re-run in this
   dispatch, exit 0, 1.70 s warm, one Agda process under the pane's set
   caliber `-A64m -I0 -M2g` (`agents/tasks/LJ-1-572/runs/w3-4.out`). Its
   `unfold-1`, `unfold-2` and `sq-bare` check the three hops by `refl` and by
   bare ascription of the parameter, so the chain is checked, not quoted.

Neither fact changed. Nothing in `src/` moved between the original stop and
this dispatch. The stop in `review-of-b9-g-definable.md` is restated there,
its limit sentence kept verbatim: this is evidence and not a refutation, and
a definable `sq` would make it true.

## WHOSE RESULT THIS IS

The measurement is the earlier attempt's: the frame miss, the warm pair at
1.83 s against the killed application, the `refl` chain from
`stage-card-upper` down to `sq`, and the stop itself are all in this report
and in `review-of-b9-g-definable.md` as the earlier attempt left them, and I
claim no credit for any of it. This dispatch re-verified the two load-bearing
facts at their own `file:line`, re-ran the salvaged W3 at 1.70 s, and closed
the row the owner authorized closing.
