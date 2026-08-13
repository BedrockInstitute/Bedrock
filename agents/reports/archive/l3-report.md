# L3 sweep report: constructibility landscape (OPEN item 7), 2026-08-02

Deliverable: dev/literature/formalizations-landscape.md (421 lines), written
in the same conventions as the existing dev/literature/*.md files, passing
`python3 scripts/lint-prose.py`. Paulson and Flypitch are cross-referenced to
formalizations.md, not redone. All indices below were fetched on 2026-08-02;
"No" means "not found via the cited index on 2026-08-02".

## Per-system table (a)-(d), with evidence URLs

| System | (a) L as formal object | (b) AC-in-L | (c) GCH-in-L | (d) rud-based development |
|---|---|---|---|---|
| Metamath set.mm | No. No class constant L (only a $f variable, set.mm line 25460); zero hits for "constructible universe", "V = L", "axiom of constructibility" in the 874,496-line source. URL: https://raw.githubusercontent.com/metamath/set.mm/develop/set.mm | No. GCH-implies-AC exists but in ambient ZF: gchac "(GCH = V -> CHOICE)", "The Generalized Continuum Hypothesis implies the Axiom of Choice ... due to Specker". URL: https://us.metamath.org/mpeuni/gchac.html | No. GCH corpus is "GCH-sets" (df-gch: "Define the collection of 'GCH-sets'...") plus gchac/gchacg/gch-kn; no theorem mentions L. URLs: https://us.metamath.org/mpeuni/df-gch.html, https://us.metamath.org/mpeuni/mmtheorems107.html | No. "rud" hits are unrelated tokens (trud, biantrud, mnugrud, inagrud). URL: https://raw.githubusercontent.com/metamath/set.mm/develop/set.mm |
| Mizar MML 5.68 | No. No ZF_L/L article; "constructible" occurs only in MUSIC_S1 (music theory). Closest: ZF_FUND1/2 formalize Mostowski operations A1-A7 and prove closure-under-A1-A7 hierarchies are models of ZF (ZF_FUND2:6 "Union L is being_a_model_of_ZF"), but no L(alpha), no V=L. URLs: https://mirror.mizar-jp.org/version/current/html/zf_fund1.html, .../zf_fund2.html, https://mirror.mizar-jp.org/JFM/Vol2/zf_fund1.html, https://mirror.mizar-jp.org/JFM/Vol3/zf_fund2.html | No. Not found in the MML article/abstract corpus (1413 files searched). | No. No "generalized continuum hypothesis" anywhere in the corpus; "continuum" only in topology (TOPGEN_5:16 "card y=0-line = continuum"). URL: https://mirror.mizar-jp.org/version/current/mml.ini | No rud/J-hierarchy/fine structure. A1-A7 are the classical Godel/Mostowski precursors. ZF_COLLA is Mostowski collapse (Collapse(E,A), ZF_COLLA:def 1), not condensation. URL: https://mirror.mizar-jp.org/version/current/html/zf_colla.html |
| Isabelle AFP + ZF-Constructible | Yes, in the Isabelle distribution session ZF-Constructible (not AFP): L built from DPow via internalized satisfaction sats(A,p,Cons(x,env)); L_axioms exports upair_ax, Union_ax, power_ax, foundation_ax, replacement. AFP topic "Set theory" (18 entries) has no constructibility entry. URLs: https://isabelle.in.tum.de/library/FOL/ZF-Constructible/index.html, .../L_axioms.html, .../document.pdf, https://isa-afp.org/topics/logic/set-theory/ | Yes. AC_in_L, theorem L_implies_AC: "Every constructible set is well-ordered! Therefore the Wellordering Theorem and the Axiom of Choice hold in L!". URL: https://isabelle.in.tum.de/library/FOL/ZF-Constructible/AC_in_L.html | No. No GCH theory in the session; "condensation" absent from document.pdf; GCH is Paulson's stated future work (cross-ref formalizations.md). URL: https://isabelle.in.tum.de/library/FOL/ZF-Constructible/document.pdf | No. "rud" absent from document.pdf; AFP entries (Forcing, Independence_CH, Transitive_Models) contain no rud. URL: https://isa-afp.org/entries/Transitive_Models.html |
| Lean mathlib4 + community | No. mathlib4 declaration index (66 MB) has no Lset/DPow; the only "L" declaration is Archive/Hairer.html#L; "Constructible" hits are topology/algebraic geometry. ZFC/Basic.lean is "A model of ZFC" (ZFSet, choice from Lean's axiom). URL: https://leanprover-community.github.io/mathlib4_docs/declarations/declaration-data.bmp, https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/SetTheory/ZFC/Basic.lean | No. | No. No GCH declarations; "continuum" is only SetTheory/Cardinal/Continuum.lean (cardinality of the continuum). | No. No "rud" path in mathlib4 or mathlib3 trees. |
| Coq/Rocq | No. opam-coq-archive (636 package dirs) has no constructible package; coq-zfc is Werner's Aczel encoding "The axioms of ZFC are then proved and thus appear as theorems", file list has no L. URL: https://api.github.com/repos/coq/opam-coq-archive/git/trees/master?recursive=1, https://raw.githubusercontent.com/coq/opam-coq-archive/master/released/packages/coq-zfc/coq-zfc.8.10.0/opam | No. | No. Only GCH-related mechanization is Kirst-Rech CPP 2021 GCH-implies-AC: "two Coq mechanisations of Sierpinski's result that the generalised continuum hypothesis (GCH) implies the axiom of choice (AC)". URL: https://www.ps.uni-saarland.de/extras/sierpinski/ | No. |
| Naproche | No. No L/V=L in the naproche repo (493 files) or examples; set-theory library covers ZFC axioms, ordinals, cardinals, cofinality; Von Neumann hierarchy exists (L03-Von_Neumann_Hierarchy.ftl), not L. URLs: https://github.com/naproche/naproche (tree), https://naproche.github.io/formalizations.html | No. | No. GCH exists only as an assumed axiom in the Penquitt set-theory library: L13-GCH.ftl "Signature. GCH is an atom. Axiom. GCH iff forall kappa /in /Card 2 ^ kappa = Plus[kappa]", and L20 "Theorem Silver. Let kappa /in /BigSingCard. Let GCH below kappa. Then 2 ^ kappa = Plus[kappa]"; no L involved. URL: https://raw.githubusercontent.com/naproche/FLib/master/SetTheory/Library/L13-GCH.ftl, .../L20-Silvers_Theorem.ftl | No. |

## Verdict on the GCH-in-L virginity claim

Not refuted; hardened. As of 2026-08-02, across Mizar, Metamath, Isabelle AFP
(plus the Isabelle/ZF Constructible session), Lean mathlib and community
projects, Coq/Rocq, and Naproche, the only formal object L is Paulson's
Isabelle/ZF Constructible session, which proves ZF-in-L and AC-in-L but
contains no GCH-in-L and no condensation lemma; GCH appears elsewhere only as
an assumed axiom or ambient-theorem corpus (Metamath gchac, Kirst-Rech GCH-to-
AC, Naproche L13-GCH), never as "L models GCH". The digest's GCH-in-L
virginity claim therefore survives this sweep, now bounded by the searched
indices and repositories on 2026-08-02 rather than by the fetched corpus, and
still worded "not found via ...", never as flat nonexistence.

## Searches that failed or were inconclusive

- mizar.uwb.edu.pl and mizar.org: connection timeouts on 2026-08-02; used the
  official mirror mirror.mizar-jp.org (MML 5.68, Mizar 8.1.11, 1412 articles,
  html dated 2022-03-02). Post-2022 MML versions could not be checked
  directly.
- mmlquery.mizar.org and mmlquery.mizar.uwb.edu.pl: unreachable; searched the
  mirror's full abstract/source corpus (1413 files) directly instead.
- isa-afp.org search page: JavaScript shell with no static results; used the
  topic index (isa-afp.org/topics/logic/set-theory/) as the library's own
  index.
- mathlib4_docs /find endpoint: JavaScript-driven; fetched and searched the
  underlying declaration index (declarations/declaration-data.bmp) instead.
- coq.inria.fr/opam/www search endpoints: returned only the JavaScript shell;
  used the opam-coq-archive repository tree as the package index instead.
- Lean community sweep: limited to the leanprover-community org listing plus
  con-nf README and Flypitch (cross-referenced); no claim about unindexed
  personal repositories.

## Deliverable line count

dev/literature/formalizations-landscape.md: 421 lines.
