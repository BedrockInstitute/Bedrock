# LJ-0.7 report: Devlin II.5 digested into the literature

Status: COMPLETE. Read-only on `src/`. No Agda run. No commit. No push.
Written incrementally (C-22): the digest skeleton landed first, then each
section filled as the reading landed.

Deliverables: `dev/literature/devlin-II5.md` (new, 626 lines) and rows 20
to 22 appended to `dev/literature/BIBLIOGRAPHY.md`.

Verdict: the digest answers the `[LJ-1.12]` question from the source. The
condensation argument needs level-hood at Sigma-1 strength with a Sigma-0
matrix, uniformly Delta-1 at limit levels. It does not need a Delta-0
witness at the satisfaction leaves. The full answer is section 2 of the
digest. This report summarizes it and points at the evidence.

## 1. THE SPINE: 5.1 to 5.4

The digest quotes each statement in full (digest sections 1.1 to 1.5). The
report states them briefly with the citation:

5.1 (`dev2.txt:1071-1078`): for amenable M and a substructure N, N is
Sigma-n-elementary in M iff every non-empty set meets N, where the set is
defined by a Sigma-1 formula with a Pi-(n-1) matrix and parameters from N.
The proof is in the chapter.

5.2 (`dev2.txt:1148-1155`): for limit alpha, X ≺₁ L_alpha gives unique pi
and beta ≤ alpha with (i) pi an isomorphism onto L_beta, (ii) pi fixing
transitive subsets of X pointwise, (iii) pi(x) ≤_L x. The object X is
extensional, not transitive. The proof collapses X via 1.7.1, then transfers
the Sigma-1 level statement along the collapse.

5.3 (`dev2.txt:1329-1335`): the set of elements definable in L_alpha from X
is the smallest elementary substructure containing X. The proof uses the
least-witness formula over the <_L order.

5.4 (`dev2.txt:1357-1360`): that hull has size max(|X|, omega), by counting
the formulas of the parameter language.

The chain 5.5 to 5.8 (`dev2.txt:1369-1406`) turns the spine into GCH:
5.5 puts subsets of L_alpha (alpha < kappa) into L_kappa; 5.6 applies 5.5 at
kappa+ with alpha = kappa and reads GCH off |L_(kappa+)| = kappa+.

## 2. WHAT THE ARGUMENT REQUIRES OF THE LEVEL STORY

The digest section 2 lists each step with its strength. The report gives the
summary:

Step A: extensionality of X needs Sigma-1 elementarity at one existential.
Step B: the collapse needs the Collapsing Lemma for an extensional
well-founded structure, with the transitive-fixing clause.
Step C: level-hood transfer needs three things. Level-hood must be
Sigma-1 with a Sigma-0 matrix. The Sigma-1 form must be uniformly Delta-1
at limit levels, with the witness inside the carrier. The Sigma-0 matrix
must be absolute for transitive sets, and the Sigma-1 statement must move
along Sigma-1 elementarity and the collapse.
Step D: the hull needs a definable well-order of the level.
Step E: the counting needs the parameter language to have max(|X|, omega)
formulas.
Step F: 5.5 needs condensation parts (i) and (ii), |L_alpha| = |alpha|, and
initial-ordinal arithmetic.
Step G: part (iii) and 5.9 to 5.11 need the well-order uniformly
Sigma-1/Delta-1 and its transfer along the collapse.

The direct answer to `[LJ-1.12]`: a Delta-0 witness for the satisfaction
leaves is not needed. Devlin's level formula H(x, alpha) = exists f [G(f,
alpha) and x = f(alpha)] is Sigma-1 with a Sigma-0 matrix
(`dev2.txt:679-686`). What IS needed is a bounded object-level description
of the Def step inside that matrix, with the bound K(u), the finite
sequence set, inside the carrier (`dev2.txt:593-630`). The `[LJ-1.2]`
probe's missing facts, the bounded descriptions of the code set and the
table, are the project-side analogues of that substrate. The argument does
not pin the substrate's shape.

## 3. THE ENGINE

The digest section 3 names twelve items. The load-bearing one is item 7:
the level-recursion machinery 2.2 to 2.8, D, Def, G, H and gamma maps to
L_gamma, all uniformly Delta-1 at limit levels. The Chapter I citations
behind it are the Collapsing Lemma 1.7.1, Sigma-0 absoluteness 1.9.15, the
language-analogue translation 1.9.11, the satisfaction machinery 1.9.10,
the KP-Recursion Theorem 1.11.8, and reflection plus amenability. The
well-order of L, 3.1 to 3.5, is a second engine for the hull and part (iii).

## 4. DEF TOWER OR EITHER TOWER, PER STEP

DD4's reading instruction is answered in digest section 4, one row per
step. The report states the outcome:

The condensation template 5.1 to 5.6 is shared. Extensionality, the
collapse, absoluteness, the transfer, the ordinal bookkeeping, the counting
and the cardinal chain are either-tower steps. The per-tower content is two
objects: the level-hood certificate and the definable well-order. On the
Def tower both run through syntax and satisfaction. On the J tower both run
through generation data, the S-step and the producer triples. This is
D-26's dichotomy applied at the level formula and at the well-order.

## 5. THE WIDENED SECTIONS

II.2.4 to II.2.7: BEARS DIRECTLY. They are the engine 5.2 consumes.
II.1.1(vii): BEARS, as the counting half of 5.5 and 5.6. It is generic
cardinal arithmetic. 5.9 to 5.11: BEAR, as the cheap condensation
instances for the wing's single application. They add no new level-story
requirement.

## 6. UNRESOLVED OCR, WITH BOTH CANDIDATES, AND THE JECH 13 CROSS-CHECK

Digest section 6 carries the full list. Resolved against the printed page:
5.2's hypothesis and part (iii)'s inequality, 5.5's bound, 5.3's
least-witness formula, and the 5.9/5.11 classes. UNRESOLVED: the carrier
subscripts in 5.2's lines (c) and (j), with the candidates named in the
digest, and the displayed matrix of 2.2, with the statement-level content
legible.

The Jech 13 cross-check agrees on every load-bearing statement: 13.17 for
condensation, 13.20 for the hull and GCH. The one divergence is the
engine: Jech certifies level-hood by the Goedel-operation adequacy
sentence, syntax-free; Devlin certifies it by internalized satisfaction.
That divergence is D-26's dichotomy.

## 7. ERRATA

The known-error list does not reach II.5. The error class that bears on the
engine is the satisfaction layer behind II.2.4, Sat with no Delta-1 version
in BS. The errata bind the internalized certificate, not the ambient
argument. The OCR doubts of section 6 are not book errors. The two classes
stay separate.

## 8. WHAT THE RETIRED ROUTE CONCLUDED, AND WHETHER IT SURVIVES

The retired route's useful residue survives: the II.5 route decomposition
(JOURNAL `:1022`), the crossing as the widest unmeasured term, and the T130
warning that the Def-side story must carry the internalized
definable-powerset step. Its failed residue does not: the successor-free
story with the Def-step as top collapses to false recognition (`[LJ-1.11]`
F1), and the crossing band that rode it is re-priced at 5.0 to 5.1k.

## 9. LITERATURE USED

Read in full: `dev/literature/digest.md`, `j-hierarchy.md`,
`primary-sources.md`, `devlin-errata.md`, `BIBLIOGRAPHY.md`,
`_build/literature/dev2.txt`, `_build/literature/jech13.txt`, and the
printed pages 78 to 85 of `devlin-ch2.pdf` via tesseract. Consulted:
`fine-structure.md` and `rudimentary-functions.md` for their SZ 5.2 to 5.4
references, which are projecta lemmas, not Devlin II.5. NOT read, with
reasons, in digest section 9.

Took: the corpus record of the II.5 fetch, the errata scoping, the J-side
engine summary, and the Jech 13 anchors.

## 10. ARCHIVE USED

`archive/dev/TASKS-archived.md` rows 119, 165, 266 and 268. `archive/dev/
JOURNAL-archived.md` lines 1022, 492 to 498 and 1756 to 1760.
`archive/dev/DECISIONS-archived.md` lines 51 to 52.
`_build/l3.32-t130-report.md` lines 26 to 33. `dev/LESSONS.md` D-10, D-26,
P-l and C-22. Each is listed with what it supplied in digest section 10.

## 11. WHAT I AM NOT SURE OF

The list is in digest section 11. The two items that could bite a builder:
the unreadable carrier in 5.2's line (c), and whether the project's coding
can supply the bounded Def-step description at the strength the digest
states. The second is `[LJ-1.12]`'s price to discover.

## WORKING TREE NOTE

`src/L/Hull.lagda.md` is modified in the tree. I did not touch it. A
sibling build, `[LJ-1.14]` (the F3 fix, Tarski-Vaught at a non-transitive
carrier), holds that file. My scope was `dev/literature/devlin-II5.md`,
`dev/literature/BIBLIOGRAPHY.md` and this report, and nothing else changed
under my hand.
