# LJ-1.129: adversarial review of the mathematics, [LJ-1.60] to [LJ-1.127]

tier: fable 5, maximum effort. Mathematics only. No master edited. No
commit. No Agda process ran: the tree carries an uncommitted edit to
`src/L/Condensation.lagda.md`, so any check would re-elaborate a 7k-line
master on the sibling's quiet machine. Every claim below is marked
MEASURED (read at the cited line, or a recorded machine result) or
INFERRED (my composition or judgment).

## 0. LEAD FINDING

**The wing's central theorem cannot serve the ruled endpoint from where
it now stands, in either direction, and the one verified entry hides
this because it is degenerate at every load-bearing point.**

Three facts compose into this, each independently checkable:

1. **Devlin 5.5 assumes V = L. The delivered statement dropped that
   premise and pays for it with ambient injection hypotheses.**
   Devlin: "Assume V = L. Let kappa be a cardinal ..."
   (dev/literature/devlin-II5.md:147-149). The delivered
   `BoundedSubsetAt` instead demands the untruncated ambient pairing
   `sq` at every infinite delta with delta in sucV alpha
   (src/L/BoundedSubset.lagda.md:1388-1390) and the untruncated ambient
   injection `absorbs` (src/L/BoundedSubset.lagda.md:1392). MEASURED.
   Under V = L Devlin gets both from the definable well-order. The
   ambient V of this development does not supply them: [LJ-1.107] found
   the honest `sq` constructible at initial ordinals only
   (dev/PLAN.md:586), and [LJ-1.114] proved the truncated form cannot
   pass Upper's induction (dev/PLAN.md:593). MEASURED (recorded).
2. **The hypothesis set is therefore supplied only at alpha = omega.**
   The demand set of `sq` at the site is exactly {omega}
   (dev/PLAN.md:595, [LJ-1.116]), and ProbeLJ1117A.agda:57-71 pays it
   with the numeral pairing. MEASURED. Devlin 5.6 applies 5.5 at
   alpha = kappa for EVERY infinite cardinal kappa
   (devlin-II5.md:164-166). At any alpha > omega the demand set
   contains non-initial ordinals, where no delivered or priced route
   supplies `sq`. So the theorem reaches the CH instance at most, and
   no row prices the gap between that and GCH. MEASURED demand shape
   (src/L/StageCardinal.lagda.md:277-283, 396-403, 530-566); the
   unsatisfiability verdict is INFERRED from the two recorded
   measurements and holds until someone builds a new route.
3. **The conclusion feeds no internal statement.** DD1 rules the
   endpoint "stated internally" (dev/PLAN.md:167), and the delivered
   cardinal hypothesis is ambient: `IsCardinal kappa = no ambient
   injection of kappa into a member` (src/L/BoundedSubset.lagda.md:
   1046-1047). [LJ-1.91] recorded the mismatch in so many words: "the
   internal omega-1-L does not provably satisfy it" (dev/PLAN.md:570).
   No PLAN row prices the conversion from the ambient conclusion
   `x in Lset kappa_Hartogs` to the internal GCH. MEASURED (grep of
   dev/PLAN.md; rows 568-608 read in full).

And the entry that produced the recent confidence does not test any of
this, because:

4. **The only instantiation is degenerate.** Site: kappa = ambient
   Hartogs of omega, alpha = omega, x = the empty set
   (src/ProbeLJ194A.agda:1186-1233; consumed at
   src/ProbeLJ1119A.agda:47-64). MEASURED. At x = empty:
   - The conclusion `theorem : x in Lset kappa`
     (src/L/BoundedSubset.lagda.md:1621-1622) is provable by delivered
     lemmas alone. The same master proves the same composition at lam:
     `∅∈Lλ` (src/L/BoundedSubset.lagda.md:1215-1217) is Lset-mono over
     `one∈α` and `∅∈Lset1`, and kappa satisfies the same premises the
     composition uses (ordinal, not in omega). MEASURED components;
     the one-line transfer to kappa is INFERRED, and no part of it
     touches Devlin55.
   - `absorbs` is trivial: the empty set is in Lset omega, the union
     collapses extensionally, and the injection is a transport
     (src/ProbeLJ1118A.agda:68-77, module AbsorbsIn). The branch the
     real consumer needs, x NOT in Lset alpha, is recorded by that
     probe's own header as "the term this dispatch could not write"
     (src/ProbeLJ1118A.agda:17-25). MEASURED.
   - `levelIn` and `cover` are still abstract parameters at the site
     (src/ProbeLJ1119A.agda:73-76), so not even the degenerate instance
     is closed. MEASURED.

**What this is not.** It is not a refutation of any delivered proof: I
found no false theorem in the window, and the Devlin55 body is a
faithful rendering of 5.5's cardinal chain (section 6). The drift is at
the statement level: the theorem's hypotheses bind it to the ambient V,
the ambient V cannot pay them beyond omega, and the ruled endpoint
lives inside L where Devlin pays them from the well-order. The route to
GCH runs through content that the current statement shape excludes and
nothing prices.

## 1. Q1: Has repeated D-30 hollowed the theorem out? Is the site degenerate?

**Statement: NOT hollowed. Evidence: YES, degenerate.**

The statement survived the five D-30 applications intact. `Devlin55`
has no parameters, but `BoundedSubsetAt` binds kappa, alpha, x and all
hypotheses as module parameters (src/L/BoundedSubset.lagda.md:
1385-1395), which is universal quantification. Moving parameters
between the two modules changed nothing mathematical. MEASURED.

Two of the D-30 moves were repairs of false generality, not narrowing:

- The pre-[LJ-1.103] `absorbs-subset` over all alpha was machine-refuted
  at alpha = empty, so Devlin55 was vacuous before the repair
  (dev/PLAN.md:580-582). The added premise alpha not in omega matches
  Devlin's own setting (5.5 is about infinite cardinals). MEASURED.
- The [LJ-1.117] `sq` restriction to sucV alpha0 matches what the proof
  consumes: the body needs the stage-size chain at alpha only, and the
  beta side is handled by the collapse injection, never by
  stage-card-upper at beta (src/L/BoundedSubset.lagda.md:1578-1583).
  MEASURED. No conclusion changed (dev/PLAN.md:596).

But the site entry certifies almost nothing:

- The body of `Co` is generic in x and does not branch on it, so its
  elaboration at the site is a real type-check of generic code.
  MEASURED (the body, src/L/BoundedSubset.lagda.md:1408-1622, read in
  full). That is plumbing value.
- The instance PROVES nothing: the conclusion at x = empty is derivable
  without the machinery (section 0, item 4). Any confidence of the form
  "the site entry closes, so the theorem stands on ground" is
  misplaced. What the entry verifies is joint WELL-TYPEDNESS of the
  hypotheses, at the unique point where each restricted hypothesis is
  contentless.
- Joint SATISFIABILITY at any instance the GCH chain uses (x a subset
  of Lset alpha that is not a member of it) is untested, and the
  absorbs branch it needs is recorded unwritten
  (src/ProbeLJ1118A.agda:17-25). MEASURED.

**Answer: the theorem is still general; the evidence base under it is
one vacuous point. Say "the telescope closes at a degenerate site", not
"the site entry closes".**

## 2. Q2: Did the eleven repairs preserve the content? YES.

The refuted originals were premise-free closure demands over unbound
sets, for example tmKeyK: `(k : S) -> k in K-slot` with no premise,
refuted at k = K-slot itself by ∈-irrefl
(src/ProbeLJ195A.agda:3-14). Such a type is empty at EVERY frame, so
the pre-repair frame assumed falsehood: its `out` could never fire at
any real site. The repair did not weaken a working theorem; it made
the frame satisfiable for the first time. MEASURED.

The tied forms add exactly the memberships the row sites hold:

- Tied shape: `succK : ... -> ar in K -> succU ...`,
  `keyK : ... -> ar in K -> a in K -> keyU ...`
  (src/L/Condensation.lagda.md:3797-3801). MEASURED.
- The rows discharge the premises from the code decomposition: codesK
  yields (arK, aK) from the code's membership, and keyK fires at those
  witnesses (src/L/Condensation.lagda.md:3740-3764). MEASURED.
- In the frames the five tied key facts are DERIVATIONS from sucK and
  pairK (SuccKeyTies, src/L/Condensation/UpperAgree.lagda.md:49-75;
  applied at src/L/Condensation/TwelveAgree.lagda.md:229-267), so they
  are not hypotheses at all. MEASURED.
- The frame's conclusions kept their types: `out : twelveAt -> twelveB`
  and `back` (src/L/Condensation/TwelveAgree.lagda.md:294-338), and the
  bounded formulas (sixB, twelveB) are built from the same clause
  formulas as before the repair. MEASURED.
- ProbeLJ1112A applies the frame at the consumer telescope and forces
  `F.out` to elaborate (src/ProbeLJ1112A.agda:410-441). MEASURED.

This mirrors Devlin exactly: the K(u)-bound closure facts hold for
members of K, never for all sets (devlin-II5.md:246-255). A weaker
hypothesis makes the agreement frame a stronger theorem, and the rows
still close. The tied forms let nothing weaker through.

**One honest caveat, and it is not about the repairs:** the zero-metas
instantiation supplies 29 consumer-side hypotheses that are NOT
discharged (dev/PLAN.md:591-592, [LJ-1.112]/[LJ-1.113]); sucK and
envSetK are still hypotheses (src/ProbeLJ1112A.agda:307-318;
dev/PLAN.md:599, 603). "Zero unsolved metas" is a telescope fact, not a
supply. See Q5.

## 3. Q3: Is the truncated square law enough? At the site YES; for the theorem NO.

- The restricted `sq` (domain sucV alpha0,
  src/L/StageCardinal.lagda.md:15-19) is exactly what Upper's induction
  consumes: LimitStep invokes `sq alpha` at each recursive stage
  (src/L/StageCardinal.lagda.md:277-283), and every stage lies below
  alpha0. MEASURED. At alpha0 = omega the demand set is {omega} and the
  supply is honest (ProbeLJ1117A.agda:49-71). MEASURED. So the
  restriction does the mathematical work Devlin's proof needs AT THAT
  POINT, and no conclusion weakened.
- The difficulty did not dissolve; it moved to the next instantiation,
  and it has already resurfaced once TODAY: the unwritten
  x-not-in-Lset-alpha branch of `absorbs` reduces to stage-card-upper
  at alpha, "i.e. honest sq at every infinite ordinal, the
  [LJ-1.107]/[LJ-1.114] wall" by the probe's own record
  (src/ProbeLJ1118A.agda:17-25). MEASURED.
- The recorded wall is route-relative, not absolute. [LJ-1.107]'s
  failure is specific to extracting an injection from the TRUNCATED
  least-bijection witness. Classically, ZF proves the square law at
  every infinite well-ordered ordinal without choice, and Devlin's own
  1.1(vii) runs under V = L where the <_L-least bijection is definable
  and extraction needs no truncation. The project owns the matching
  machinery class (leastOf over SWO, the L well-order chapter). This
  cure is INFERRED and unpriced; I state it as the direction consistent
  with the literature, not as a price.

**Answer: enough for alpha = omega, and honestly so. Not enough for
Devlin 5.6, which needs the law's consequences at every infinite
cardinal, and the sidestep left that obligation standing with no row,
no price and no named owner.**

## 4. Q4: Is the ambient cardinal the right cardinal? NO.

- `IsCardinal` is ambient by type: ambient presentation, ambient
  functions (src/L/BoundedSubset.lagda.md:1046-1047). The consumer
  opens the V-structure (src/L/BoundedSubset.lagda.md:56). MEASURED.
- The conclusion `x in Lset kappa` is an ambient membership statement
  about the L-hierarchy inside V. As a lemma this is legitimate: an
  ambient cardinal IS an L-cardinal (an L-injection would be an ambient
  injection; INFERRED, classical), so the instance proved is true.
- But the ruled endpoint is internal: DD1, "The endpoint is the SAME L
  satisfying GCH, stated internally" (dev/PLAN.md:167); DD2 "both
  stated in L" (dev/PLAN.md:41-42, 168). The internal GCH quantifies
  over L's cardinals, and the L-successor cardinal of an infinite
  L-cardinal need not be an ambient cardinal. The project measured the
  gap itself: "IsCardinal is ambient, so the internal omega-1-L does
  not provably satisfy it" (dev/PLAN.md:570, [LJ-1.91]). MEASURED.
- I searched PLAN for any row that prices the conversion from the
  ambient conclusion to the internal statement, or that rules the
  ambient reading as the intended endpoint semantics. There is none
  (dev/PLAN.md rows 568-625 read; grep for cardinal/internal).
  MEASURED absence.

**Answer: the theorem has become a claim about V that mentions L. It is
a true and Devlin-shaped claim, and the ambient Hartogs construction
([LJ-1.94]) is real mathematics with no choice used. But nothing
connects its conclusion to `L |= GCH` stated in L, and the one recorded
fact about that connection is negative. Either a conversion row gets
priced (ambient-to-internal, or re-founding the wing's cardinal notion
inside L), or the wing is building toward a statement the endpoint does
not name.**

## 5. Q5: levelIn, cover, and the 0.6k figure

**Are they the right hypotheses? YES in shape.** Checked against the
digest: `levelIn` is Devlin 5.2(i)'s forward chain conclusion, L_gamma
in M for each collapse ordinal (devlin-II5.md:102-106, dev2 chain (c)
to (i)); `cover` is the reverse inclusion M inside the union of levels
(devlin-II5.md:106-110, chain (j) to (q)). The delivered `Condense`
consumes them precisely where Devlin's proof consumes the two
inclusions: beta-succ, piX inside Lset beta, Lset beta inside piX
(src/L/BoundedSubset.lagda.md:959-1034). MEASURED correspondence. They
are not convenient weakeners; they ARE the heart of condensation,
stated as hypotheses. The honest reading: the wing has proved
"condensation follows from condensation's hard part", and everyone on
the record knows it ([LJ-1.121], dev/PLAN.md:601).

**Is 0.6k believable? ONLY IN PART.** The [LJ-1.123] decomposition
(_build/lj-1.123-report.md:30-45) is genuine work and its delivered-
component map checks against the tree (I verified the LevelHood,
IsoInv, DownReflect, HullElemDown, Condense citations by reading the
master). Two soft spots:

1. The figure's own basis is read evidence with no probe, said plainly
   in the report (P-l applies, and the report cites it). [LJ-1.124]
   then measured GO on the bounded level-graph decode at 147 lines,
   which converts the FIRST band only.
2. The second band, "certificate truth at the hull ordinals, with the
   bound in the stage, 0.10-0.25k", must contain (a) the choice of the
   concrete witness K and (b) the supply of the frame's ~28
   undischarged closure hypotheses at that K, which [LJ-1.113] classed
   "PROVABLE 1, NEW CONTENT 28" (dev/PLAN.md:592). Since then someEnv
   closed ([LJ-1.120]) and envSetK got a HOME but not a supply
   (dev/PLAN.md:599, 603). Twenty-plus closure facts at a concrete K,
   even at one shared pattern, plus the Devlin 2.6(ii) analogue (the
   witness set exists INSIDE the stage, devlin-II5.md:218-223) is
   plausibly a band of its own at the project's delivered rates.
   INFERRED: the 0.6k center is optimistic and the honest band should
   carry the 28-fact supply as an explicit term. The widest unmeasured
   term of the re-priced chapter is now this supply, not the decode.

**Answer: right hypotheses, correctly named as the wall; the 0.6k
figure is a projection whose largest remaining term is not the one its
probe measured.**

## 6. WHAT I CHECKED THAT HELD (the clean half of the bill)

- **Devlin55.Co's body is Devlin 5.5's proof, step for step.** Hull of
  Lset alpha union {x} at a successor-closed lam (5.4's M); collapse;
  condensation via the two hypotheses; the size chain as injections:
  beta into Lset beta (stage-card-lower), transported along ext into
  piX, then piX into alpha through the propositional collapse fibre and
  the least code (InvColl + CodeSelect + CodeCount,
  src/L/BoundedSubset.lagda.md:1059-1141, 1426-1583); the cardinal step
  by trichotomy against cardkappa (src/L/BoundedSubset.lagda.md:
  1594-1603) matching "|gamma| = |alpha| < kappa implies gamma < kappa";
  x fixed by the collapse because X is transitive
  (src/L/BoundedSubset.lagda.md:1584-1592), which is Devlin part (ii)
  applied exactly as at devlin-II5.md:152-157. MEASURED, read in full.
- **The injection route around |L_beta| = |beta| is sound and avoids a
  hidden sq demand at beta.** Only the LOWER half is used at beta;
  the upper half is used at alpha only. MEASURED
  (src/L/BoundedSubset.lagda.md:1578-1583, 1529-1530).
- **IsoInv** proves satisfaction invariance along the collapse in both
  directions by induction over all fourteen connectives, with
  surjectivity used only where Devlin uses it (universal and
  existential cases). Read in full
  (src/L/BoundedSubset.lagda.md:152-319). MEASURED.
- **HullExt** derives extensionality of the hull through the difference
  formula and hull-closure, which is Devlin Step A (extensionality of X
  from elementarity, devlin-II5.md:187-195) done at Sigma-1 strength.
  Read in full (src/L/BoundedSubset.lagda.md:1235-1358). MEASURED.
- **Condense's beta bookkeeping** (the ordinal separation, beta-succ
  from cover plus rank, sucV closure, both inclusions, extensionality)
  matches Devlin's lim(beta) step and the M = L_beta assembly. Read in
  full (src/L/BoundedSubset.lagda.md:903-1034). MEASURED.
- **StageCardinal's Bound/LimitStep/Upper**: the counting is Devlin's
  |L_alpha| = |alpha| upper half in injection form, by ∈-induction with
  the omega base from finite tallies. Read in full. The only external
  demand is `sq`, correctly threaded. MEASURED.
- **The twelve-row frames compose**: LowerAgree and UpperAgree conjoin
  into TwelveAgree without re-proving rows, and the composer
  instantiates at the consumer telescope. MEASURED
  (src/L/Condensation/TwelveAgree.lagda.md:269-338,
  src/ProbeLJ1112A.agda:410-441).

## 7. FINDINGS NOT ASKED ABOUT

1. **The confidence chain "entered at the site" needs a language rule.**
   Three PLAN rows in the window read as progress on the theorem
   (LJ-1.117 "no conclusion changed", LJ-1.118 "site value built",
   LJ-1.119 "entered") while the entered instance is the vacuous one.
   None of the rows is false. Their sum reads stronger than their
   content. A row that enters a theorem at a degenerate point should
   say so in the row.
2. **sucK and envSetK are supply debts of the frame with no site
   supplier**, recorded as hypotheses in the probes
   (src/ProbeLJ1112A.agda:307-318; dev/PLAN.md:603). They join the 28
   of Q5 item 2.
3. **Nothing consumes LevelHood yet** (the Sigma-1 level-hood formula,
   src/L/BoundedSubset.lagda.md:74-146): its adequacy against the
   actual Lset is exactly the un-built decode-plus-truth content of Q5.
   MEASURED (also recorded at _build/lj-1.123-report.md:227-235).
4. **A positive worth keeping:** the machine-refutation practice
   ([LJ-1.95], [LJ-1.97], [LJ-1.101]) caught two vacuous theorem
   frames (the untied rows, the unrestricted absorbs) that a
   prose-level review would have passed. That practice is the reason
   this window's proofs are trustworthy at the type level.

## 8. WHAT I CHECKED (inventory)

Read in full: src/L/BoundedSubset.lagda.md (1627 lines);
src/L/StageCardinal.lagda.md; src/L/Condensation/TwelveAgree.lagda.md;
src/L/Condensation/UpperAgree.lagda.md; src/ProbeLJ1119A.agda;
src/ProbeLJ1117A.agda; src/ProbeLJ1121A.agda; src/ProbeLJ1112A.agda;
dev/literature/devlin-II5.md; _build/lj-1.123-report.md.

Read in part (structure plus the cited regions):
src/L/Condensation.lagda.md (head, template, keyU/succU, ForallAgree,
the NegAgree-class row body at 3740-3764);
src/L/Ordinal/SquareLaw.lagda.md (head, Init, the delivery tail);
src/ProbeLJ194A.agda (head, OrdSWO, Hartogs cardκ, SiteAt);
src/ProbeLJ1118A.agda (header and AbsorbsIn); src/ProbeLJ195A.agda,
src/ProbeLJ1111A.agda, src/ProbeLJ1122A.agda, src/ProbeLJ1124A.agda,
src/ProbeLJ1125A/B.agda (headers and key modules); dev/PLAN.md section
0, section 3 (DD1, DD2, DD5, DD24), section 11 rows LJ-1.90 to
LJ-1.129.

Not done: no Agda run (reason at top); no git-history diff of the
frames' pre-repair conclusions (the conclusion-formula stability is
argued from the current tree plus the probes' verbatim-copy records,
INFERRED at that one point).

## 9. ARCHIVE USED

Not read directly. Archive content entered through
dev/literature/devlin-II5.md sections 8 and 10, which survey
archive/dev/TASKS-archived.md (T84, T130, T259, T263),
JOURNAL-archived.md (T5, T48), and DECISIONS-archived.md (D31/D32),
at file:line there. Took: the II.5 decomposition (T5), the ⊤̇-step
refutation record (T84), and the T48 note that 5.5 consumes
condensation parts (i)(ii) only, which section 6 of this report
re-verified against the delivered body.
