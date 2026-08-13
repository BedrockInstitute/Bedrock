# [L3.32-T22] The W3 sealing design probe (break the walls, then re-price)
tier: codex (default)

GOAL: `[T19]` ran W3's gate and found the order formula's CONTENT real and its
statement layer instant, while every materializing step walled. Its own
diagnosis is the lead: these are not the P-d class the retiring cone recorded
but the OTHER P-series class, the one that cone's seals exist for. So this is a
DESIGN probe, not a build: take T19's three walled shapes, attack each with the
law book's sealing cures, and report which cure moves which wall and what W3
should be funded at if the cures hold. Breaking even one of the three is worth
the run; breaking none is a valid and important result.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): `src/ProbeW3Seal.agda` (untracked) and
`_build/l3.32-t22-report.md` ONLY. No master, never `Everything`.
SCOPE (read, in order): `_build/l3.32-t19-report.md` IN FULL (the three walls,
their exact shapes, and the wall trail: reproduce its shapes, do not invent
new ones), `src/ProbeW3.agda` (the walled probe itself: its green statement
layer is your starting point), `_build/l3.32-t14-report.md` (what W3 is and
what the order must deliver), `src/L/Rud/Order.lagda.md` (the delivered
producer order and, importantly, HOW it survives: read its seals),
`src/L/WellOrder/Base.lagda.md` (the least-witness machinery that walls when
normalized), `src/ProbeRehome.agda` (the pattern that absorbed a truncated
membership into a proposition-valued goal, which T21 reused successfully),
`dev/LESSONS.md` (BINDING and the point of the exercise: R-35 small indices,
R-36 opaque-unfolding read lemmas, R-38 seal at the birth site, I-5 written
branch types, P-i layer caps and huge-argument rules, D-16 the inner-world
reading, and the restricted-carrier and named-head cures recorded from the
R3a walls).

THE THREE ARMS, each with its named cures to try in order:

**ARM 1, the index at the concrete presentation** (T19: forming a member's
index at the concrete tower exhausted an 8 GB heap). Cures: state everything at
a VARIABLE level with the presentation abstract (R-35 small indices, the
restricted-carrier statement, P-i's rule that heavy objects sit at variables or
stuck terms), and instantiate only behind a seal. Question to answer: is the
heap event a property of the STATEMENT or only of the instantiation?

**ARM 2, the key-shape case analysis** (T19: it normalizes the least-element
search and hangs even with a trivial body, at BOTH carriers). This is the
highest-value arm because it hangs abstractly, so it is not an instantiation
artifact. Cures: replace the case analysis by a named helper with a WRITTEN
type (I-5); seal the least-witness machinery at its BIRTH SITE and read it
through opaque-unfolding read lemmas (R-38 then R-36); and the re-home
pattern, absorbing the truncated result into a proposition-valued goal rather
than casing on it. Report which of the three moves the wall and by how much.

**ARM 3, comparison types carrying a concrete ordinal** (T19: they hang).
Cures: take the ordinal as a VARIABLE with its ordinality a separate
hypothesis, never a concrete pair (R-37, P-i's huge-argument rule).

METHOD, binding: for every arm, record the BEFORE and AFTER wall time and heap
behaviour, since the re-price rests on the difference, not on the verdict word.
An arm that stays walled after two distinct cures is recorded precisely and
abandoned; do not spend the budget on one arm.

CONSTRAINTS: `GHCRTS="-A64m -I0 -M12g" agda <file>`, ONE Agda process at a
time (nothing else is running; the heavy cap is yours). Per-arm abort budget
240 s: a hang past it is the arm's result, not a failure. STOP-LINE 400 probe
lines. No postulate, no hole, no TERMINATING. C-6 controls on any claim that a
wall is gone (a green that typechecks vacuously proves nothing: check the
statement is still the one you meant). No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t22-report.md`; final message = compressed verdict):
per-arm BROKEN or STILL WALLED with the before-and-after measurements and the
cure that did it; whether arm 2's abstract hang is curable, since that is the
one that decides whether W3 is a design problem or a real cost; **what W3
should now be funded at in both calibers if the surviving cures are adopted**,
against T19's 1.1-2.7k naive; and the prescription a W3 build brief would
mandate, stated as first-formulation rules.
