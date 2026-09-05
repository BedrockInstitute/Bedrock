# review-of-rank-coded

The NO-GO stands.

`[LJ-1.490]` measured the range clause, the fourth `InjCode` conjunct,
at the bound `[LJ-1.486]` delivered. The reading `from-out`
typechecks (`Probe490.agda`, exit 0). The range clause does not
inhabit: a close that treats the pair-in-bound as the second-
component-in-codomain is `[UnequalTerms]`
(`runs/w3-false-close.out`, exit 42).

The finding: `PairBound.bnd` is a bounding STAGE (`LsetS β' oβ'`). It
holds the rank pairs. It is not the codomain ORDINAL `C` (`LsetS β
oβ`, the bounding ordinal of the rank). The range clause wants the
second component of a pair in the carve to be a member of `C`. The
bridge is the adequacy of `rankFo` to `swo-rank`, which
`[LJ-1.475]` left (`lj-1.475-report.md:236-253`). `PairBound.below`
is the forward direction (a member and a rank yield a pair in the
bound); it does not read a pair in the bound back to a member of `C`.

So the bound serves the carve, not the code. The two need different
sets: a bounding stage for the carve, and the bounding ordinal for the
code. The next brief must fund the adequacy first. Then the second
component of a pair in the carve is a member of `C`, and the range
clause closes.

The codomain is `C`, the bounding ordinal, so `b` in the obligation
is determined, not free. The obligation's telescope changes from a
free `b` to `b = C` when the adequacy lands.

The obligation `rank-coded` has no term. The witness meter reports
`1 UNRESOLVED of 1` (`runs/witness.out`, exit 1). `src/` is
untouched. No commit, no push. This review does not close the task;
the critic reads this file.
