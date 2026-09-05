# LJ-1.283: which over-bar masters carry the seal shape, and what does each seal cost

tier: opus (in-harness-subagent-mode). I ran scripts/dispatch_policy.py before dispatching: in-harness-subagent-mode is IN FORCE, clock-selected, PEAK, Beijing window 14:00 to 18:00.

## GOAL

THE REPOSITORY OWNER ASKED, in their own words: can we dispatch agents to bisect and SEAL all the over-bar modules? Answer it with measurement, not opinion.

The answer is not a flat yes. Sealing is a measured lever with a measured law and at least one measured failure, and the law says which sites pay.

## WHAT THE RECORD ALREADY SAYS, and every line is a claim to check (C-44)

- Sealing took a FOL.Coding module application from over 600 s to 0.3 s, at least 2,300x, per dev/LESSONS.md. Find that entry and read it whole.
- [LJ-1.152]'s commit line reads "GO at 2.50 s, and the seal was never the cure". Read that report. What made the seal fail THERE?
- [LJ-1.214] measured sealing moving 83 ms on the telescope component, one of three cheap levers measured void.
- [LJ-1.281] measured TODAY, on src/L/Cardinal.lagda.md: control 100.50 s, R-35 cure 15.53 s, opacity cure 9.16 s. The seal WON, by 6 seconds over the alternative and 91 over the control. Its report is agents/tasks/LJ-1-281/lj-1.281-report.md.
- P-y is the law that decides: the price of a seal is set by how many definitions look INSIDE the formula, not by how many NAME it. Read the FULL entry in dev/LESSONS.md.
- R-36 and P-i also bear. Read them.

## THE MASTERS OVER THE BAR

[LJ-1.218] measured every wing master. The bar is 0.010514 s/line. Over it, at agents/tasks/LJ-1-218/lj-1.218-report.md:56-67:

  src/L/Condensation.lagda.md              0.0198   132.28 s
  src/L/Condensation/TwelveAgree.lagda.md  0.0177     8.77 s
  src/L/Condensation/UpperAgree.lagda.md   0.0183     5.60 s
  src/L/Condensation/LowerAgree.lagda.md   0.0172     5.25 s
  src/L/Ordinal/StageArith.lagda.md        0.0126     0.94 s
  src/V/Presentation.lagda.md              0.0368     0.66 s
  src/L/Ordinal/SquareLaw.lagda.md         0.0107     8.28 s   NOISE, crosses the bar
  src/L/BoundedSubset.lagda.md             0.0112    15.78 s   NOISE, crosses the bar

Those figures predate today. FOUR NEW MASTERS LANDED TODAY and two are far over the bar: src/L/Coding/EnvSupply.lagda.md at 833 lines and 482.73 s, 0.5795 s/line, 55.1x the bar; and src/L/Cardinal.lagda.md at 189 lines and 100.57 s, whose cure [LJ-1.282] is landing right now, so EXCLUDE Cardinal from your survey and say you did.

EnvSupply is the big one and nobody has looked inside it for this shape.

## WHAT TO BRING BACK

1. THE TRIAGE. For each master above except Cardinal: does it carry the seal shape at all? The shape is a transparent definition whose body is walked by a conversion check, typically a well-order, a union representation, a coding formula, or a heavy set forced into normalization. Name the candidate at file:line, or say the master does not carry the shape and why.

2. THE P-y PRICE FOR EACH CANDIDATE. Count the definitions that must see INSIDE it, NOT the ones that name it. Give both counts, because the gap between them is P-y's whole point. Grep the tree. A consumer reaching the formula through a named reader needs no unfolding.

3. ONE MEASUREMENT, ON THE BEST CANDIDATE ONLY. Do not measure eight masters; you do not have the hours and src/L/Condensation.lagda.md alone is 132 s cold. Pick the candidate with the best ratio of seconds-at-stake to P-y price, build ONE paired arm in your own task directory, and measure it: control first, then treated, at least three kept cold runs each, order reversed between cycles. Say plainly which you picked and why the others lost.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- THE TRIAGE COMPLETES AND ONE ARM IS MEASURED. Report the table, the price per candidate, and the one measurement. Then the owner has a ranked list and I write build briefs from it. STOP.
- NO MASTER CARRIES THE SHAPE. Say so plainly with evidence. Then today's Cardinal result is a one-site win and the owner should hear that the answer to their question is NO for the rest, which is worth the dispatch.
- A CANDIDATE'S P-y PRICE IS HIGH EVERYWHERE. That is the [LJ-1.152] outcome repeating and it is a real answer. Say which masters and what the inside-count is.
- THE MEASURED ARM DOES NOT HELP. Report it MEASURED. C-36: a failed substitution is not a proof of impossibility, so say what you could not write.
- A WALL. A single agda invocation past 30 MINUTES is a wall: interrupt, report elapsed seconds, bisect.

## CONSTRAINTS

- ONE agda process at a time, always GHCRTS="-A64m -I0 -M8g". The cap is C-12's and is NEVER raised. Report a heap exhaustion as a wall. Report the machine load beside every absolute figure.
- LAND NOTHING. Write only in agents/tasks/LJ-1-283/. src/ is forbidden for probes (I-5) and scripts/check-probes.py enforces it. Never src/Everything.lagda.md, never dev/PLAN.md, never dev/ledger.toml.
- A SIBLING IS LIVE in agents/tasks/LJ-1-282/ and it is editing src/L/Cardinal.lagda.md. Do not touch either. That is also why Cardinal is out of your survey.
- Do not touch src/L/Choice/Name.lagda.md. DD23 blocks a pending change.
- P-l binds hard here: a cure measured at one site is a HYPOTHESIS at another. Today's 91-second win on Cardinal says nothing about EnvSupply until someone measures EnvSupply.
- P-t: an average hides the term. A master's whole-file rate does not tell you which definition costs.
- Create agents/tasks/LJ-1-283/lj-1.283-report.md in your first five minutes and fill it incrementally (C-22).
- Never commit, never push, never git checkout ., git stash, git reset --hard, git clean. Do not run make check.
- Run .venv/bin/python scripts/lint-prose.py --check and scripts/lint-agda.py --check on what you write. NO EM DASH in any language.
- Evidence is file:line. Write ASD-STE100. Mark every negative MEASURED or INFERRED, in those words.
- Run .venv/bin/python scripts/rules.py --for probe and read every statement; open the full entry for any law you act on.

## DD4

Maximize the code the two proofs share, and write it generic. One rule, two ends, no metric and no checker. A seal is a change to a SHARED definition when the definition is shared, so say per candidate whether the seal would be inherited by both towers or paid once per tower. NAME YOUR AXIS (C-46): DD4's own axis is AC-against-GCH, fixed in code at scripts/ledger.py:50, and that report ran for the first time today at 41.1 percent shared.

## ARCHIVE (DD18)

agents/tasks/LJ-1-281/lj-1.281-report.md read WHOLE; agents/tasks/LJ-1-218/lj-1.218-report.md:56-67; agents/tasks/LJ-1-152/ read for why the seal failed there; agents/tasks/LJ-1-214/lj-1.214-report.md for the 83 ms; dev/LESSONS.md P-y, R-36, P-i as FULL entries; archive/dev/TASKS-archived.md, taking SHAPE and never a claim, since the 2,300x seal was learned on the retired route. Return an ARCHIVE USED section naming ONE line read per archived file.

## LITERATURE (DD18)

Nothing in the literature governs elaboration cost. Say so in one line and return a LITERATURE USED section.

## SCOPE (read)

agents/tasks/LJ-1-281/lj-1.281-report.md FIRST, whole.

## SCOPE (write)

agents/tasks/LJ-1-283/ only.

## RETURN

Lead with the RANKED LIST: each over-bar master, whether it carries the seal shape, its P-y inside-count, and the seconds at stake. Then the one measured arm, control first. Then why the others lost. Then what [LJ-1.152]'s seal failure teaches about which of these would fail the same way. Then the DD4 answer per candidate with its axis. Mark every negative MEASURED or INFERRED.

End your final message with: the ranked list in one line each, and the one measured delta.
