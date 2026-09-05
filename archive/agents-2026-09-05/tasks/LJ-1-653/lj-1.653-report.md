# [LJ-1.653] report: is step 4 TRUE at ordinals

GO. Exit 0. `0 UNRESOLVED of 1` (`runs/witness-final.out:2`).

## 1. THE VERDICT

**Step 4 at ordinals is TRUE, and it is NOT an independent obstruction.**
It is the SAME residue the consumer's own goal already owes.

I did not refute it, and I did not attack it as an isolated equation.
I reduced it. The reduction is a term, it typechecks, and every
hypothesis it takes is either delivered in the tree today or is a
residue the chapter already carries in its own words.

The obligation is at `agents/tasks/LJ-1-653/Probe653.agda:299`:

    step4-at-ord-status : ... (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
      → HullStage.HoodCompleteP ... φ₀
      → HullStage.HoodSoundP ... φ₀
      → HullStage.HullClosedLsetOrd ...
      → HullStage.PiCommuteLsetOrd ...

`PiCommuteLsetOrd` (`Probe653.agda:172`) is `[LJ-1.462]`'s step 4
(`agents/tasks/LJ-1-462/Probe462.agda:140-142`) restricted to ordinal
`y`, the same type as `[LJ-1.649]`'s `PiCommuteLsetOrd`
(`agents/tasks/LJ-1-649/Probe649.agda:233-235`).

**THE THREE HYPOTHESES, AND WHAT EACH ONE COSTS.**

1. `HullClosedLsetOrd` (`Probe653.agda:166`) is step 2 in the type
   `[LJ-1.647]` DELIVERED, taken as a module hypothesis under the
   predecessor clause. Not new work.
2. `HoodCompleteP φ₀` (`Probe653.agda:224`): the hull believes `Lset y`
   is the level at `y`, for an ordinal `y` of the hull.
3. `HoodSoundP φ₀` (`Probe653.agda:229`): the collapse is CORRECT about
   level-hood. If the collapse believes `v` is the level at `γ`, then
   `v ≡ Lset γ`.

**NEITHER 2 NOR 3 MENTIONS `C.π`, AND THAT IS WHY THE REDUCTION IS
DECISIVE AND NOT A RESTATEMENT.** `φ₀` is pinned parameter-free
(`Formula (⊥* {ℓ-suc ℓ}) 2`), so the relabelling along the collapse
fixes it: `embed-fixed` (`Probe653.agda:218`) proves
`mapFo CIso.I.g (embed φ₀) ≡ embed φ₀`. Hypothesis 2 speaks only of `M`
and `Lset`. Hypothesis 3 speaks only of `C.πX` and `Lset`. Step 4 is the
equation that joins `π` to `Lset`, and neither half of the price
contains it.

**THE PAIR IS NOT TRIVIALLY SATISFIABLE, so the term is not vacuous.**
At `φ₀ = ⊤̇` hypothesis 2 holds and hypothesis 3 says every member of
`C.πX` is the level at every ordinal of `C.πX`, which fails at any
collapse with two ordinals. At `φ₀ = ⊥̇` hypothesis 3 holds and
hypothesis 2 fails. The pair pins `φ₀` to a real level-hood formula.

## 2. THE SECOND TERM, AND WHY IT RE-PLANS THE CAMPAIGN

`levelin-from-hood-status` (`Probe653.agda:313`) takes the SAME
`HoodSoundP φ₀`, plus its existential companion `HoodExistsP φ₀`
(`Probe653.agda:277`), and delivers `LevelIn` (`Probe653.agda:263`),
which is the consumer's own goal at `src/L/BoundedSubset.lagda.md:917`.

    levelin-from-hood-status : ... → HoodExistsP ... φ₀ → HoodSoundP ... φ₀
                             → LevelIn ...

**There is no step 4 in that chain, and no step 2 either.** So the
`[LJ-1.462]` four-step decomposition is not the only road to `levelIn`,
and step 4 is not a toll gate on the road it shares.

`[LJ-1.649]` called step 4 "the campaign's real stop"
(`agents/tasks/LJ-1-649/lj-1.649-report.md:361`). That reading is
CORRECTED by this task, and in the cheaper direction: step 4 is real,
but it is not a separate stop. It and `levelIn` are one stop.

## 3. WHAT `[LJ-1.477]` HIT, AND WHY IT HIT IT

`[LJ-1.477]` drove the two computation laws at one argument and stopped
at their join, `JoinSteps` (`agents/tasks/LJ-1-477/Probe477.agda:90-93`).
It recorded that it "did not prove the type false"
(`agents/tasks/LJ-1-477/lj-1.477-report.md:188`).

The measurement here says why that route stops. `JoinSteps` asks a
`sett` of `π`-images of hull-filtered members to equal a union of `𝒟ₒ`
of levels. That is a DEFINABILITY transfer, and no computation law
carries one. The elementarity route does not touch either constructor.
`[LJ-1.477]`'s report names elementarity three times
(`agents/tasks/LJ-1-477/lj-1.477-report.md:80`, `:315`, `:318`) and its
probe takes no elementarity hypothesis: `Elementary` does not occur in
`agents/tasks/LJ-1-477/Probe477.agda`. The brief it worked under forbade
an absoluteness hypothesis
(`agents/tasks/LJ-1-477/lj-1.477-report.md:183-184`). **The obstruction `[LJ-1.477]` measured is an obstruction of
its route and not of the statement.**

## 4. WHAT IS NEW AND GREEN, BEYOND THE OBLIGATION

**`π-ord` (`Probe653.agda:130`): the collapse carries ordinality
FORWARD, unconditionally.**

    π-ord : (x : S) → IsOrd x → IsOrd (C.π x)

It rests on `π-trans` (`Probe653.agda:113`), the same fact for
transitivity, which rests on `π-member-in` (`Probe653.agda:97`). The
tree's own `π-member` (`src/V/Collapse.lagda.md:63-71`) DROPS the
witness's membership in the argument; `π-member-in` keeps it, and the
whole of part 2 needs it.

This is load-bearing, not decoration. `HoodSoundP` asks for `IsOrd γ` at
`γ = C.π y`, and without `π-ord` the target's own right-hand side,
`Lset (C.π y)`, is not known to be a level at all. The tree had
`πX-trans` (`src/V/Collapse.lagda.md:89`) for the RANGE only.

**`π-ord` IS THE CONVERSE OF `[LJ-1.649]`'s FIFTH FACT.** 649 named
`PiReflectsOrd`, `(y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd (C.π y) → IsOrd y`
(`agents/tasks/LJ-1-649/Probe649.agda:222-223`), as unbuilt and as the
price of the ordinal keystone. The forward direction is now built, needs
no hull membership, and cost 34 lines with `π-member-in`. The reverse
direction is untouched by this task.

## 5. THE ONE LEG THAT IS STILL OWED, PRICED

`HoodSoundP` splits into two legs, and I MEASURED the first.

**LEG 1 IS FREE.** `hoodSound-Δ₀-leg` (`Probe653.agda:153`) is
`AbsπX.abs₀` and nothing else. The body is the delivered term with no
adapter:

    module AbsπX = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ C.πX) C.πX-trans

    hoodSound-Δ₀-leg : ∀ {n} {φ : Formula CIso.I.SPM n} → Δ₀ φ
                     → (δ : CIso.I.SPM ^ n)
                     → (δ CIso.I.⊨ᵖᵐ φ) ≡ ((map fst δ) AbsπX.⊨ᵛ φ)
    hoodSound-Δ₀-leg = AbsπX.abs₀

That it typechecks by that body is the measurement: the restricted
structure `FOL.Absoluteness.Single` builds at `C.πX` is the SAME
structure `CollapseIso` reads, so `abs₀` lands on `HoodSoundP`'s
antecedent directly. Transitivity is the only hypothesis
`FOL.Absoluteness.Single` asks for
(`src/FOL/Absoluteness.lagda.md:57-59`), and `C.πX-trans` is delivered
(`src/V/Collapse.lagda.md:89`). **So the Δ₀ transfer from the collapse
to the AMBIENT hierarchy costs zero.**

**LEG 2 IS THE ONE THAT IS OWED.** `Lset-only` is stated at the L-CLASS
carrier, not at the ambient one: `src/L/Hierarchy.lagda.md:334-335` for
the statement, and `src/L/Hierarchy.lagda.md:78-79` for the carrier,
`module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`. Leg 1 lands in
the AMBIENT reading. So leg 2 is one of exactly two facts, and the next
brief should choose between them:

- **(a) `C.πX ⊆ L`.** With it, `abs₀` at the class carrier closes the
  gap with no new content. Nothing in this task prices it.
- **(b) An ambient form of `Lset-only`.** THIS ONE WAS BUILT AND THEN
  CUT. `dev/ARCHIVE.md:285` records the Crossing section of
  `L.Condensation`, cut in place by D32 at commit `3f5001e`, which
  "stated the ambient-reading form of `Lset-only` at the class carrier"
  and factored it into `TransferL` and `ValueIsL`. Its price is on the
  books: `ambientOnly-from` carried 92 percent of the module's profile
  and the cut removed 138.7 s
  (`archive/dev/JOURNAL-archived.md:2507-2509`). The rebuild is the
  `crossing-rebuild` ledger row, trophy GCH, `dev/ledger.toml:1021-1026`.

**(a) IS ALMOST CERTAINLY THE CHEAP ONE.** (b) is a five-thousand-line
GCH-trophy row. (a) is one closure fact about collapse values. I did not
attempt either; naming the fork is this task's finding, not closing it.

`HoodCompleteP` is not new debt. It is the chapter's own named residue:
"the level-hood instantiation at the hull is the priced residue"
(`src/L/BoundedSubset.lagda.md:901-902`), against the skeleton
`[LJ-1.48]` measured at 0.0097 s per line.

## 6. W3, THE WIDEST UNMEASURED TERM

The brief named it: "Whether the collapse of a LEVEL is the level of the
collapse at an ordinal", estimated at 90 to 190 lines.

**MEASURED: the decisive miniature is 23 non-blank non-comment lines**
(`Probe653.agda:194-215` for `step4-at-ord`, plus `:242-247` for the
parameter-free wrapper). The delivered probe is 196 non-blank lines over
322, and the extra is `π-member-in`, `π-trans`, `π-ord`, the Δ₀ leg
measurement, and the second term of section 2. **The brief's estimate is
high by about a factor of four at the assembly, because the estimate
priced the JOIN of the two computation laws, which is the route
`[LJ-1.477]` took and is not the route that closes.**

## 7. W2, THE GENERIC CARRIER

Answered, and the clause is met twice over.

The whole probe sits in ONE copy of the `HullStage` telescope
(`Probe653.agda:66-71`), copied from `src/L/BoundedSubset.lagda.md:903-916`,
the same cut `Probe477.agda:44-57` and `Probe462.agda:78-90` took.
Nothing is written twice for a fixed `lam` or a fixed `X`.

`step4-at-ord` (`Probe653.agda:194`) is generic in the FORMULA as well.
It takes `φ` and the two adequacy halves at `φ`, so it holds at whatever
level-hood formula the chapter finally instantiates. The parameter-free
wrapper (`Probe653.agda:242`) is the instance, not a second proof.

I did not meet a conflict between W2 and a deadline.

## 8. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and untouched here. One Agda process at a time. Every
dependency warm. All runs from the repository root. The probe interface
was deleted before every kept run.

**Floor first, as the slot instruction requires on a heavy object.**
The frame alone, with imports and the module instantiations and no
obligation: `runs/floor-0.out`, 3.42 s, 730,611,712 bytes, exit 0. The
frame imports `L.BoundedSubset`, which `[LJ-1.477]`'s frame did not, and
that is where the floor sits. **The obligation adds about 0.4 s to a
3.4 s floor**, so this object is frame-bound and not term-bound. I
trimmed the imports to the names the rows actually use.

Three forced rechecks of the delivered file:

| run | wall s | peak RSS bytes | exit |
|---|---|---|---|
| `runs/final-1.out` / `.time` | 3.71 | 838,189,056 | 0 |
| `runs/final-2.out` / `.time` | 4.02 | 838,221,824 | 0 |
| `runs/final-3.out` / `.time` | 3.79 | 838,254,592 | 0 |

Median wall **3.79 s**. Median peak RSS **838,221,824 bytes**. Each
printed `Checking`. No heap event, and no restructuring was needed.

Earlier kept runs, not among the three: `runs/p-0.out` (4.04 s,
824,492,032 bytes, exit 0, the general-formula version);
`runs/p-1.out` (4.25 s, 752,369,664 bytes, exit 0, after the
parameter-free forms landed); `runs/p-2.out` (exit 42, one
`[UnequalTerms]` at `Probe653.agda:154`, a SCOPE slip and not a
mathematical one: `_^_` imported bare from the parameterised
`FOL.Semantics` takes its module parameters as explicit arguments. The
fix opens `_^_` from `AbsπX` instead); `runs/p-3.out` (exit 0, the fix);
`runs/recheck-1.out` to `runs/recheck-3.out` (3.82, 4.15, 3.89 s), the
rechecks of the version before section 5's Δ₀ leg was added.

Witness meter, one obligation: `runs/witness-final.out`,
`pass exit=0 3.27s`, `0 UNRESOLVED of 1`, `probe_red=False`. This
worktree has no `.venv`; the meter ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`.
I did not add a dependency and I did not create a local `.venv`.

## 9. WHAT THE NEXT BRIEF NEEDS

1. **Do not fund a proof of step 4 as an isolated equation.** Fund
   `HoodSoundP` leg 2, and fund it as fork (a): is `C.πX ⊆ L`? That one
   fact closes step 4 AND `levelIn` together, through the two terms this
   probe delivers.
2. **`HoodCompleteP` is the chapter's own residue and it moves nothing
   new onto the books** (`src/L/BoundedSubset.lagda.md:901-902`).
3. **`PiReflectsOrd` is still unbuilt and is still needed** by the
   `[LJ-1.649]` route. `π-ord` gives the forward direction only.
4. **A refutation is not reachable at this frame, and this is a
   measurement, not a shrug.** A counterexample must name a concrete
   `lam`, `X` and `y` and then decide a membership of `M = H.T.Hull`.
   `Hull` is the image of the term algebra's `val`
   (`src/L/Hull.lagda.md:337-339`), so its membership is a TRUNCATED
   existence over codes. Nothing in the tree computes it. Any future
   refutation attempt at step 4 has to defeat that first, and it should
   be priced before it is dispatched.
5. This task changed nothing in `src/`.

## 10. GATES

Run individually while the work was live, as the Boundary requires:

- `scripts/gate/lint-agda.py --check`: clean, no output.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (9907
  tracked files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: clean, no output.

I did not run `make check`. I did not commit and I did not push.

## ARCHIVE USED

- **`dev/ARCHIVE.md` READ.** `dev/ARCHIVE.md:285`: "The Crossing section
  stated the ambient-reading form of `Lset-only` at the class carrier."
  This is the row that prices `HoodSoundP` leg 2, fork (b), in section 5.
- **`archive/dev/JOURNAL-archived.md` READ.**
  `archive/dev/JOURNAL-archived.md:2130`: "formula's decodes nor an
  ambient form of `Lset-only` is delivered." Same fork, from the stop
  that preceded the cut. `archive/dev/JOURNAL-archived.md:2507` carries
  the cut's own figure, "The check time falls 150.2 s to 11.5 s.
  `ambientOnly-from` carried 92".
- **`archive/dev/LJ-dispatch-index.md` READ.**
  `archive/dev/LJ-dispatch-index.md:97`: "| LJ-1.49 | Discharge levelIn
  and collapseCode, price the rest | BOTH CURES LANDED | collapseCode
  DELETED. levelIn and cover survive, Mext enters. One leaf transfer
  measures 150.13 s |". It confirms `levelIn` and `cover` are the two
  surviving hypotheses of `Condense`, which is what section 2's second
  term aims at.
- **`archive/dev/JOURNAL.md` DECLINED.** Surveyed by grep, not read: no
  occurrence of the target shape and no occurrence of "commut". Its
  eight "ambient" hits are outside the `Lset-only` thread.
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read. It is the
  archived process document and carries no mathematics; zero hits for
  both "commut" and "ambient".

## LITERATURE USED

- **`dev/literature/devlin-II5.md` READ.**
  `dev/literature/devlin-II5.md:102`: "The chain (c) to (q) then runs:
  for each ordinal γ of the collapse, the Σ₁", and
  `dev/literature/devlin-II5.md:228`: "4. Transfer along elementarity
  and the collapse: the Σ₁ statement". This is the SAME chain the two
  terms of this probe assemble: Σ₁ statement, transferred along
  elementarity to the hull and along the collapse, then Σ₀ absoluteness
  at a transitive carrier, then the graph read back as `v = L_γ`. The
  source confirms the route and does not confirm the price.
- **`dev/literature/digest.md` DECLINED.** Not read. It is the whole-book
  index; `devlin-II5.md:18` already names the section of it that applies.
- **`dev/literature/truncation-and-selection.md` DECLINED.** Not used.
  This task took no truncated choice and selected no code.
- **`dev/literature/devlin-errata.md` DECLINED.** Not used. No step of
  the reduction rests on a disputed passage.
- **`dev/literature/geology.md` DECLINED.** Not used. Set-theoretic
  geology is not on this route.
