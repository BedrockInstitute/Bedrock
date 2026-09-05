# LJ-1.297: the DD25 adversarial review of `q`'s machine refutation

tier: opus (pi-subagent-mode), the switch's ADVERSARIAL row. I ran scripts/dispatch_policy.py before dispatching: pi-subagent-mode is IN FORCE, PINNED by the owner 2026-08-15. Its default head is pi and its adversarial head is in-harness opus. The target was written by pi on glm-5.3, so DD17's invariant holds: the critic is not the author.

## GOAL

[LJ-1.293] returned a NEGATIVE and DD25 fires: attack it before I act on it.

**Its verdict: `q` is FALSE, refuted BY MACHINE.** The term is `q-false` at agents/tasks/LJ-1-293/ProbeLJ1293A.agda:132-133, exit 0, mean 2.51 s over three kept runs. It derives Empty from

    IntendedQ = Seq.LsetGraphAt {2} zero (suc zero) ≡ embed P1241.φ₀

at ProbeLJ1293A.agda:121-122, and the carrier check is `ambient≡ = refl` at :82-83.

**Why this matters more than one probe.** `q` is the condition under which `amb` is supplied, and `amb` is the LAST open parameter of [LJ-1.7], which is LJ-1's blocking row. A conditional supply whose condition is refuted is not a supply (C-38 as extended). So this return says the phase's terminus is further away than the record had it, and it says so on the strength of one 133-line probe.

## WHAT YOU ATTACK, and it is the NEGATIVE, not the task

DD25's four questions.

**1. IS THE REFUTATION CORRECT ON ITS OWN TERMS?** Re-derive it. Read ProbeLJ1293A.agda WHOLE. Run it yourself. **The claim to attack hardest is `IntendedQ`: is it really `q` at the intended instantiation, or is it a DIFFERENT equation that happens to be false?** The report rests on `Graph := LsetGraphAt` from ProbeLJ1184B.agda:48-51. **If that reading is wrong, the whole refutation is about the wrong object.**

**2. IS THE CARRIER CHECK SOUND?** `ambient≡ = refl` at :82-83 asserts the port's carrier IS probe A's ambient carrier. **A refl between two things that only look alike is exactly the C-45 shape this campaign keeps meeting.** Check what each side actually elaborates to.

**3. DID THE BRIEF CAUSE THE OUTCOME?** I wrote it. I named FALSE as "the most valuable outcome" and told the agent that a refutation would re-price the phase. **That is a strong prior handed to an agent, and C-39 says a brief's prohibition binds harder than its goal.** Ask whether the brief steered it toward a refutation it would not otherwise have reached.

**4. IS THERE A CURE THE RETURN MISSED?** The report names the obligation as

    q' : (γ : Vec A.R.SC 2) → ⟨ A.ambient γ (embed φ₀) ⟩
       → ⟨ A.ambient γ (Graph {2} zero (suc zero)) ⟩

the one-direction implication that `go` actually spends, and cites [LJ-1.244]: `q'` as a HYPOTHESIS typechecks and `amb` comes out (ProbeLJ1244A.agda, exit 0), but as a DEFINITION the goal is stuck (ProbeLJ1244B.agda:75, exit 42). **The blocking term is the coding-transfer bridge at the ambient carrier, and the report says its CLASS-CARRIER analogues are DELIVERED at src/L/Condensation.lagda.md:6617-6654 and :6795-7045.**

**THAT LAST SENTENCE IS THE MONEY.** If class-carrier analogues are delivered, ask what it costs to instantiate them at the ambient carrier. **P-l binds: a construction delivered at one carrier is a hypothesis at another.** But a delivered analogue is a much better starting point than nothing, and nobody has priced that move.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE REFUTATION HOLDS.** Say so. A review that AGREES is a real result and it buys confidence in a finding the phase is about to re-plan around. Then price the q' route. STOP.
- **THE REFUTATION IS ABOUT THE WRONG OBJECT.** Name the correct object at file:line. That is the most valuable outcome here.
- **q IS FALSE BUT amb IS SUPPLIABLE ANOTHER WAY.** Name the route.
- **q' IS ALSO FALSE.** Then [LJ-1.7] needs a different architecture and the owner must hear it. Say what would have to change.

## CONSTRAINTS

- YOU MAY RUN AGDA. Both Agda slots are free: [LJ-1.292] and [LJ-1.293] have returned. Run ONE agda process at a time, always GHCRTS="-A64m -I0 -M8g". The cap is C-12's and is NEVER raised. Report a heap exhaustion as a wall. Report the machine load beside every absolute figure.
- A single agda invocation past 30 MINUTES is a wall: interrupt, report elapsed seconds, bisect.
- Write ONLY inside agents/tasks/LJ-1-297/. src/ is forbidden for probes (I-5). Never src/Everything.lagda.md, never dev/ledger.toml, never dev/PLAN.md, never src/L/Choice/Name.lagda.md (DD23).
- agents/tasks/LJ-1-293/ is a FROZEN record: read it, copy from it, write nothing into it.
- THREE SIBLINGS ARE LIVE: [LJ-1.294] in agents/tasks/LJ-1-294/, [LJ-1.295] which is MOVING scripts/ right now, and [LJ-1.296]. Touch none of them. Because scripts/ is being reorganised under you, invoke checkers by name and expect paths to change mid-run; if a script vanishes, say so rather than working around it.
- Create agents/tasks/LJ-1-297/lj-1.297-report.md in your first five minutes and fill it incrementally (C-22).
- Never commit, never push, never git checkout ., git stash, git reset --hard, git clean. Do not run make check.
- Run lint-prose.py --check and lint-agda.py --check on what you write. NO EM DASH in any language. DD23 freezes mathematical prose.
- Evidence is file:line. Write ASD-STE100. Mark every negative MEASURED or INFERRED, in those words.
- Run .venv/bin/python scripts/rules.py --for review and read every statement.

## THE RULES THIS CHAIN EARNED

C-45. An assumed equation in a telescope is an idiom when refl closes it and a HYPOTHESIS when it does not. AUDIT THE INSTANTIATION. Question 2 is that law aimed at the refutation's own refl.

C-38 as extended. A hypothesis is discharged when something SUPPLIES it, and a conditional supply is not a supply.

C-42. A refutation measures the site it names and never how far it extends.

C-44. Every figure in this brief is [LJ-1.293]'s and you must re-derive each one.

D-10. Price the truth of a recorded residue before pricing its proof. The record now says q is false; your job includes checking that the record is right.

## DD4

Maximize the code the two proofs share, and write it generic. One rule, two ends, no metric and no checker. [LJ-1.293] answered on the port's L-against-ambient axis and said so, which is what C-46 asks. Check that its axis is the right one for this object: amb is the ambient half of a cross that reads one formula at two carriers, so the axis is the SUBJECT here rather than a label. NAME YOUR AXIS.

## ARCHIVE (DD18)

agents/tasks/LJ-1-293/lj-1.293-report.md read WHOLE, and its ProbeLJ1293A.agda read WHOLE. agents/tasks/LJ-1-244/ProbeLJ1244A.agda and ProbeLJ1244B.agda:75, the hypothesis-versus-definition split. agents/tasks/LJ-1-243/lj-1.243-report.md section 3.1, which named q'. agents/tasks/LJ-1-242/, which first read the equation false. archive/dev/TASKS-archived.md, taking SHAPE and never a claim. Return an ARCHIVE USED section naming ONE line read per archived file.

## LITERATURE (DD18)

dev/literature/devlin-II5.md splits II.5 into twelve rows and amb is clause (a) at the ambient carrier. Say whether Devlin needs this equation at all, or whether the port introduced it. If the port introduced it, that reframes everything. Return a LITERATURE USED section.

## SCOPE (read)

agents/tasks/LJ-1-293/lj-1.293-report.md FIRST, whole.

## SCOPE (write)

agents/tasks/LJ-1-297/ only.

## RETURN

Lead with ONE word: HOLDS or WRONG. Then your own run of the refutation term. Then whether IntendedQ is q at the intended instantiation, at file:line. Then whether the refl carrier check is sound. Then whether my brief steered the outcome. Then the price of the q' route through the delivered class-carrier analogues. Then the DD4 answer with its axis. Mark every negative MEASURED or INFERRED.

End your final message with: HOLDS or WRONG, and whether amb has any route left.
