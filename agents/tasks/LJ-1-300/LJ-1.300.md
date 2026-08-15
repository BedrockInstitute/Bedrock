# LJ-1.300: the DD25 review of a defect in the TROPHY'S OWN STATEMENT

tier: opus (pi-subagent-mode), the switch's ADVERSARIAL row. I ran scripts/dispatch/dispatch_policy.py before dispatching. The target was written by pi on glm-5.3, so DD17's invariant holds: the critic is not the author.

## GOAL

[LJ-1.299] returned CIRCULAR on its own task and found something larger on the way. DD25 fires on the whole return, and the larger thing is why this review matters more than usual: **it says the GCH trophy's remaining hypothesis, as landed in src/ today, gates nothing.**

## THE THREE CLAIMS, in the order I want them attacked

**CLAIM 1, AND I HAVE ALREADY VERIFIED IT MYSELF. `SqShape` is mis-parsed.**

src/L/GCH.lagda.md:47 reads

    → ⟪ fst α ⟫ × ⟪ fst α ⟫ ↪ ⟪ fst α ⟫

`_↪_` at src/L/Cardinal.lagda.md:47 carries NO fixity declaration, so it binds tighter than `infixr 5 _×_`, and the body parses as `⟪α⟫ × (⟪α⟫ ↪ ⟪α⟫)`: an element of the carrier PAIRED WITH a self-injection.

I wrote my own minimal file, agents/tasks/LJ-1-299/ParseCheckOrch.agda, and it typechecks exit 0. It proves both halves: `snd` of the as-written form is a self-injection, and given any element the whole thing is INHABITED by the identity. **So the hypothesis gates nothing.**

**ATTACK THIS ANYWAY.** My file is a MINIMAL RECONSTRUCTION, not the real one. It defines its own `_↪_` and its own `_×_` import. **The real `SqShape` sits under `L.GCH`'s imports and module telescope, and a fixity or an operator could differ there.** Read the real thing, in place, and settle it against the real imports. **If my reconstruction is not faithful, say so: I would rather be wrong here than have the project act on a reconstruction.**

**CLAIM 2. The circularity.** `noinj²` at κ needs the square law at every infinite β ∈ˢ κ, and that is `[LJ-1.8]`'s own undischarged hypothesis. The tree's only delivered route to a square at an ordinal is `via-col-square` at src/L/Ordinal/SquareLaw.lagda.md:960, which consumes `Init`, whose fourth row is `noinj²` at that same ordinal. **Check the cycle link by link. A circularity claim is exactly the kind that is one mis-read away from false.**

**CLAIM 3. The deeper wall.** Even handed the square law, `IsCardinalL` cannot close `noinj²`. The target's probe reduces it to ONE named hole, `AmbientToCode`, the REVERSE of the move [LJ-1.294] priced. The target calls that bridge MEASURED absent and INFERRED FALSE as mathematics, on the ground that an ambient injection's graph need not be constructible. **INFERRED FALSE is a strong claim on a mathematical object. Test it. A countermodel would settle it; an argument would not.**

## WHAT FOLLOWS IF CLAIM 1 HOLDS, and this is why the review comes before the fix

**The fix is one pair of parentheses, and I have NOT applied it.** Adding them makes the trophy's hypothesis strictly stronger, which means:

- **every downstream measurement taken against the current `SqShape` is void** (C-32), including [LJ-1.286]'s Init gap table and [LJ-1.294]'s use-site analysis;
- **the trophy statement changes**, which is the owner's to rule on, not mine;
- **and it may not be the only such defect.** C-42: a refutation measures the site it names. **SWEEP `src/` for the same shape: an operator with no fixity declaration used unparenthesised beside `_×_`, `_⊎_`, `_→_` or `_≡_`.** Report the COUNT. That sweep is the most valuable thing in this task after claim 1.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **ALL THREE HOLD.** Report each with your own term, plus the sweep's count. STOP. Then the owner rules on the statement and I re-plan the phase.
- **CLAIM 1 IS WRONG.** Say exactly where my reconstruction diverges from the real `SqShape`. **That is the most valuable outcome and I want it if it is true.**
- **THE CIRCULARITY IS NOT REAL.** Name the link that breaks it. Then `[LJ-1.8]` has a route and the phase is in better shape than the return says.
- **`AmbientToCode` IS TRUE.** Then the deeper wall is not a wall and the target overstated it.
- **A WALL.** A single agda invocation past 30 MINUTES is a wall: interrupt, report elapsed seconds, bisect. NEVER raise the cap.

## CONSTRAINTS

- YOU MAY RUN AGDA. Both slots are free. ONE process at a time, always GHCRTS="-A64m -I0 -M8g", cap never raised. Report the load beside every absolute figure.
- **DO NOT EDIT src/L/GCH.lagda.md OR ANY MASTER.** The parenthesis fix is the owner's ruling and mine to apply. **If you are tempted, that is the moment to stop and report.**
- Write ONLY inside agents/tasks/LJ-1-300/. src/ is forbidden for probes (I-5).
- agents/tasks/LJ-1-299/ is a FROZEN record: read it, copy from it, write nothing into it.
- Never src/Everything.lagda.md, never dev/ledger.toml, never dev/PLAN.md, never src/L/Choice/Name.lagda.md (DD23).
- Create agents/tasks/LJ-1-300/lj-1.300-report.md in your first five minutes and fill it incrementally (C-22).
- Never commit, never push, never git checkout ., git stash, git reset --hard, git clean. Do not run make check.
- Run .venv/bin/python scripts/gate/lint-prose.py --check and scripts/gate/lint-agda.py --check. NO EM DASH in any language. DD23 freezes mathematical prose.
- Evidence is file:line. Write ASD-STE100. Mark every negative MEASURED or INFERRED, in those words.
- Run .venv/bin/python scripts/dispatch/rules.py --for review and read every statement.

## THE RULES THIS CHAIN EARNED

C-32. A cure invalidates every downstream measurement. The parenthesis fix is such a cure and it sits UPSTREAM of two tasks' conclusions.

C-42. A refutation measures the site it names and never how far it extends. Hence the sweep.

C-44. Every claim in this brief is the target's or mine, and mine is a reconstruction.

C-45. Audit the INSTANTIATION, never the telescope. A hypothesis that is inhabited outright is that law's sharpest case: the telescope looked like a real assumption.

D-10. Price the truth of a recorded residue before pricing its proof.

## DD4

Maximize the code the two proofs share, and write it generic. One rule, two ends, no metric and no checker. SqShape is stated in src/L/GCH.lagda.md, the declared gch_root. If the parse defect is real, DD4's first published figure was computed over a statement that is not the intended one. Say whether the figure moves when the parentheses go in, and NAME YOUR AXIS (C-46): DD4's own axis is AC-against-GCH.

## ARCHIVE (DD18)

agents/tasks/LJ-1-299/lj-1.299-report.md read WHOLE and its probes NoInj2.agda and Mini.agda. agents/tasks/LJ-1-299/ParseCheckOrch.agda, which is MINE and which you should treat as the least trustworthy evidence here. agents/tasks/LJ-1-294/ and LJ-1-286/, whose conclusions this would void. archive/dev/TASKS-archived.md, taking SHAPE and never a claim. Return an ARCHIVE USED section naming ONE line read per archived file.

## LITERATURE (DD18)

dev/literature/devlin-II5.md. Say what Devlin's square law actually states, and whether the intended parenthesisation matches it. If the tree's intended reading differs from Devlin's, that is a third finding.

## SCOPE (read)

src/L/GCH.lagda.md:44-48 FIRST, in place, with its imports.

## SCOPE (write)

agents/tasks/LJ-1-300/ only.

## RETURN

Lead with ONE word per claim: HOLDS or WRONG, three times. Then your own term for claim 1, against the REAL SqShape and not a reconstruction. Then the sweep's count of the same shape elsewhere in src/. Then what the parenthesis fix would void. Then the DD4 answer with its axis. Mark every negative MEASURED or INFERRED.

End your final message with: the three verdicts, the sweep count, and whether the trophy statement must change.
