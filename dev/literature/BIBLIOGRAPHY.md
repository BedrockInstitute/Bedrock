# Bibliography for the rud route

Every source from the raw sweep, plus the additional sources that were fetched
to answer the sweep's questions. Fields: citation, URL, access status (open /
paywalled / cite-only), one-line role, consumer notes file. "Fetched" means the
content was downloaded and read during this pass (2026-08-02).

## Primary sources (open, fetched)

1. Mathias, A. R. D.; Bowler, N. J. "Rudimentary recursion, gentle functions
   and provident sets." Notre Dame Journal of Formal Logic 56(1):3-60, 2015.
   - Preprint PDF (fetched, 40 pp.): https://preprint.math.uni-hamburg.de/
     public/papers/hbm/hbm613.pdf
   - Journal: https://projecteuclid.org/journals/notre-dame-journal-of-formal-
     logic/volume-56/issue-1/Rudimentary-Recursion-Gentle-Functions-and-
     Provident-Sets/10.1215/00294527-2835101.full
   - Access: open (preprint fetched; journal page not fetched).
   - Role: the modern rigorous treatment of rudimentary recursion; the
     corrected basis R0..R8; provident sets as transitive models of PROVI;
     provident levels of L and J; the Δ0-truth predicate over MW.
   - Consumed by: rudimentary-functions.md, j-hierarchy.md, devlin-errata.md.

2. Mathias, A. R. D. "Weak systems of Gandy, Jensen and Devlin." In Set
   Theory (Bagaria, Todorcevic, eds.), Trends in Mathematics, Birkhäuser,
   2006, 149-224. CRM preprint 614 (2005).
   - Preprint PDF (fetched, 76 pp.): https://ddd.uab.cat/pub/prepub/2005/
     hdl_2072_2150/pr614.pdf
   - Published chapter: https://link.springer.com/chapter/10.1007/3-7643-7692-9_6
   - Access: open (preprint fetched); published chapter paywalled.
   - Role: the corrected foundations replacing Devlin's Chapter VI; system
     hierarchy ReS, DB, BS, GJ, GJI, MW; the R0..R8 basis; the Gandy-Jensen
     Lemma; the T function; the full inventory of Devlin's errors (section 10);
     models showing BS's failures; TCo failure in Z; McAloon's question.
   - Consumed by: rudimentary-functions.md, devlin-errata.md.

3. Schindler, Ralf; Zeman, Martin. "Fine structure." In Handbook of Set
   Theory (Foreman, Kanamori, eds.), Springer, 2010 (author preprint,
   September 11, 2006; 58 pp. in the fetched PDF).
   - Author PDF (fetched, with relaxed certificate check; the server has a
     broken certificate chain): https://ivv5hpp.uni-muenster.de/u/rds/
     finestructure.pdf
   - Author page: https://ivv5hpp.uni-muenster.de/u/rds/
   - Access: open (author copy).
   - Role: the orthodox contemporary survey; rud_A schemata; J- and
     S-hierarchies; the canonical well-order; Σ1 condensation; acceptability;
     Σ1 satisfaction and Skolem functions; applications to L (acceptability,
     soundness, covering, ♦κ).
   - Consumed by: rudimentary-functions.md, j-hierarchy.md.

4. Stanley, Lee J. "Review: Keith J. Devlin, Constructibility." Journal of
   Symbolic Logic 52(3):864-867, 1987.
   - Project Euclid: https://projecteuclid.org/euclid.jsl/1183742450 (metadata
     fetched via Wayback; full text paywalled, via JSTOR for subscribers).
   - JSTOR: https://www.jstor.org/stable/2274371 (landing page fetched via
     Wayback; full text paywalled).
   - Access: paywalled. Full text NOT fetched; only bibliographic metadata and
     second-hand accounts (Mathias WS section 10; Welch draft).
   - Role: the documented error record for Devlin's book.
   - Consumed by: devlin-errata.md.

5. Mathias, A. R. D. "Provident Set Theory." Freiburg slides, 2014.
   - PDF (fetched, 59 slides): http://home.mathematik.uni-freiburg.de/
     mildenberger/freiburg2014/bildchen/mathias.pdf
   - Access: open.
   - Role: condensed statement of the provident-set theory: R0..R8, T, rud
     rec, gentle functions, provident sets, Jω provident (next J_{ω^2}),
     PROVI and its reversals, set forcing over provident sets.
   - Consumed by: rudimentary-functions.md, j-hierarchy.md.

6. Mathias, A. R. D. "Weak set theories in foundational debates."
   Philosophical Transactions of the Royal Society A 381(2248):20220009,
   2023.
   - Publisher page: https://royalsocietypublishing.org/rsta/article/381/2248/
     20220009/112375/ (bot-blocked; full text NOT fetched).
   - PubMed abstract (fetched): https://pubmed.ncbi.nlm.nih.gov/37031698/
   - Access: full text not open access per Unpaywall and Europe PMC
     (subscription required); abstract obtained from PubMed.
   - Role: contemporary survey placing the weak-systems/rud line in context
     (PROVI supports constructibility and forcing in outline).
   - Consumed by: BIBLIOGRAPHY.md (role line only; no load-bearing claims).

## Formalization precedents (open, fetched)

7. Paulson, Lawrence C. "The Relative Consistency of the Axiom of Choice
   Mechanized Using Isabelle/ZF." arXiv:2104.12674v1, 26 Apr 2021.
   - arXiv: https://arxiv.org/abs/2104.12674 (abstract page fetched)
   - PDF (fetched, 67 pp.): https://arxiv.org/pdf/2104.12674
   - Isabelle library outline (fetched, 202 pp.): https://isabelle.in.tum.de/
     website-Isabelle2021/dist/library/ZF/ZF-Constructible/outline.pdf
   - Slides (fetched, 19 slides): https://www.cl.cam.ac.uk/~lp15/papers/
     Formath/constructible-slides.pdf
   - Access: open.
   - Role: the documented precedent for the satisfaction-internalization
     route; AC-in-L formalized, GCH and ♦ explicitly left for future work;
     verdict on metatheory.
   - Consumed by: formalizations.md.

8. Han, Jesse Michael; van Doorn, Floris. "A Formal Proof of the Independence
   of the Continuum Hypothesis." CPP 2020.
   - PDF (fetched, 14 pp.): https://florisvandoorn.com/papers/flypitch-cpp-
     2020.pdf
   - Repository (fetched README): https://github.com/flypitch/flypitch
   - Access: open.
   - Role: formal independence of CH in Lean 3 via Boolean-valued models,
     Cohen forcing (¬CH) and σ-closed collapse forcing (CH); no constructible
     universe (listed as future work).
   - Consumed by: formalizations.md.

9. Han, Jesse Michael; van Doorn, Floris. "A formalization of forcing and the
   unprovability of the continuum hypothesis." ITP 2019 (extended preprint).
   - PDF (fetched, 19 pp.): https://florisvandoorn.com/papers/flypitch-itp-
     2019.pdf
   - Access: open.
   - Role: the ¬CH direction of Flypitch (Boolean-valued models over the
     regular opens of 2^ω; fundamental theorem of forcing).
   - Consumed by: formalizations.md.

## Additional sources fetched during this pass (not in the raw sweep)

10. Welch, P. D. "Syntax without arithmetic or concatenation." Draft,
    Oct 10 2012.
    - PDF (fetched, degraded symbol extraction): https://people.maths.bris.ac.
      uk/~mapdw/gj8.pdf
    - Access: open.
    - Role: secondary account of the GJ basis, the Gandy-Jensen Lemma, the
      term-simulation proof that Δ0 = rud over GJ, and of Stanley's suggested
      cure for Devlin's BS. DRAFT: treat as secondary.
    - Consumed by: rudimentary-functions.md, devlin-errata.md.

11. MathOverflow, "Devlin's 'Constructibility' as a resource"
    (question 77734), via the StackExchange API.
    - URL: https://mathoverflow.net/questions/77734/devlins-constructibility-
      as-a-resource
    - Access: open.
    - Role: corroborates that Stanley's review documented flaws in Devlin's
      initial fine-structure development; no technical detail beyond that.
    - Consumed by: devlin-errata.md (one corroborating line).

## Cite-only entries (paywalled or books; no fetching; citations only)

12. Jensen, Ronald B. "The fine structure of the constructible hierarchy."
    Annals of Mathematical Logic 4:229-308, 1972 (with erratum, ibid.
    4:443). The origin of rud functions and the J-hierarchy. Cite-only.
    (Bibliographic details as given in SZ p. 57 and WS p. 76.)

13. Devlin, Keith J. "Constructibility." Perspectives in Mathematical Logic,
    Springer-Verlag, Berlin, 1984. The standard book; Chapter VI's rud
    treatment contains the documented errors (see devlin-errata.md). Cite-only.

14. Zeman, Martin. "Inner Models and Large Cardinals." de Gruyter Series in
    Logic and Its Applications 5, 2002. Chapter 1: careful rud exposition;
    rud_A relativization. Cite-only. (Cited in SZ bibliography, p. 58, as
    [15].)

15. Gandy, R. O. "Set-theoretic functions for elementary syntax." In
    Axiomatic Set Theory II, Proceedings of Symposia in Pure Mathematics 13,
    Part II (Jech, ed.), AMS, 1974, 103-126. The basic-functions basis
    parallel to Jensen's. Cite-only. (Bibliographic details as in MB p. 40 and
    WS p. 76.)

16. Schindler, Ralf. "Set Theory: Exploring Independence and Truth."
    Springer, 2014. https://link.springer.com/book/10.1007/978-3-319-06725-4
    Textbook L treatment. Cite-only.

17. Kunen, Kenneth. "Set Theory: An Introduction to Independence Proofs."
    North-Holland, 1980. The satisfaction-route baseline (Def of L via
    satisfaction; the textbook followed by Paulson). Cite-only.

18. Jech, Thomas. "Set Theory." 3rd ed., Springer, 2003. The satisfaction-
    route baseline (Gödel operations in II.13). Cite-only.

19. Jensen, Ronald B.; Karp, Carol. "Primitive recursive set functions." In
    Axiomatic Set Theory I, Proceedings of Symposia in Pure Mathematics 13,
    Part I (Scott, ed.), AMS, 1971, 143-176. The primitive-recursive-set-
    function companion to Jensen's rud theory. Cite-only. (Cited in MB p. 40;
    also in the Freiburg slides.)

## Second-round fetch artifacts (recorded by `[LJ-0.7]`)

20. Devlin, Keith J. "Constructibility." Perspectives in Mathematical Logic,
    Springer, 1984. Chapter II (the Constructible Universe), fetched as the
    ABBYY OCR scan `_build/literature/dev2.txt` plus `devlin-ch2.pdf`.
    Access: open scan (Project Euclid "Perspectives in Logic"). Role: the
    condensation chapter II.5 and its level-story engine II.2; the sourced
    GCH-in-L derivation (Theorem 5.6).
    Consumed by: devlin-II5.md (this task), digest.md (record at
    `digest.md:513-518`), `[LJ-1.11]`.

21. Jech, Thomas. "Set Theory." 3rd millennium ed., Springer, 2003. Chapter
    13 (Constructible Sets), fetched as the typed PDF extraction
    `_build/literature/jech13.txt`. Access: open (institutional PDF hosted by
    TU Delft). Role: the typed cross-check for Devlin II.5: Goedel's
    Condensation Lemma 13.17, the adequacy sentence 13.13, the GCH theorem
    13.20.
    Consumed by: devlin-II5.md (this task).

22. Devlin, Keith J. "Constructibility." Chapter II, printed pages 78-85,
    re-OCR'd from `_build/literature/devlin-ch2.pdf` with tesseract during
    `[LJ-0.7]`. Role: resolving OCR-degraded glyphs in II.5 (5.2's part
    (iii), 5.5's bound, the 2.2 matrix region).
    Consumed by: devlin-II5.md (this task).

## Consumption map (which notes file consumes which source)

| Source | rudimentary-functions.md | j-hierarchy.md | devlin-errata.md | formalizations.md | devlin-II5.md |
| --- | --- | --- | --- | --- | --- |
| Mathias-Bowler (1) | x | x | x |  |  |
| Weak systems (2) | x |  | x |  |  |
| Schindler-Zeman (3) | x | x |  |  |  |
| Stanley review (4) |  |  | x (metadata + second-hand) |  |  |
| Freiburg slides (5) | x | x |  |  |  |
| Phil. Trans. A (6) |  |  |  |  |  |
| Paulson (7) |  |  |  | x |  |
| Flypitch CPP (8) |  |  |  | x |  |
| Flypitch ITP (9) |  |  |  | x |  |
| Welch draft (10) | x |  | x |  |  |
| MathOverflow (11) |  |  | x |  |  |
| Devlin ch. II (20) |  |  |  |  | x |
| Jech ch. 13 (21) |  |  |  |  | x |
| Devlin ch. II re-OCR (22) |  |  |  |  | x |
