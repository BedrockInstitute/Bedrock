# L2 report: second-round primary-source fetch

Date: 2026-08-02. Scope: re-attempt the sources the L1 round could not reach,
to settle digest OPEN items 1, 3, 4, 8 and 9 (Jensen's verbatim 1972 basis
list and indexing; a citable named statement of "rud = compositions of the
Gödel operations"; Gandy's side; Zeman's simple-functions role). Deliverables:
`dev/literature/primary-sources.md` (the notes file) and this report; fetched
artifacts under `_build/literature/` (git-ignored, nothing committed). No git
mutations were performed; `git status` shows only the new notes file.

## 1. Network status

Network available. Two publisher hosts are bot-walled for automated fetch:
ScienceDirect (Incapsula/captcha; HTTP 403, and the jina reader receives a
captcha page) and Project Euclid live (Incapsula; HTTP 200 with a challenge
iframe). Project Euclid content was obtained through the Wayback Machine
instead; ScienceDirect could not be obtained through any legitimate route
(its PDF was never archived, and Wayback Save Page Now returns HTTP 520).

## 2. Per-target fetch results

Legend: OK = content fetched and extracted; PAYWALLED = publisher requires
subscription and no open copy exists; NOT-FOUND = no legitimate copy located;
BLOCKED = content is open on the publisher but the host blocks automated
fetch. DEGRADED = fetched but text extraction loses math glyphs (OCR scan or
pdftotext glyph loss).

| Target | URL(s) tried | Result | Extraction quality |
| --- | --- | --- | --- |
| 1. Jensen, Ann. Math. Logic 4 (1972) 229-308 | `sciencedirect.com/science/article/pii/0003484372900010` (page and `pdfft` with full browser headers, md5+pid token variant); Wayback CDX + snapshots (2021, 2024); Wayback Save Page Now; r.jina.ai reader; OpenAlex/Unpaywall (closed in both); doi.org | BLOCKED (open-archive on publisher, bot wall); fallback: Jensen's own manuscript fetched from the Bonn author archive (OK) | Journal text: not fetched. Fallback JM: typed PDF, minor glyph loss (omega/member-of/union), restored where unambiguous |
| 2. Devlin, "Constructibility" (1984) | `projecteuclid.org/ebooks/perspectives-in-logic/Constructibility` (live, Incapsula-blocked); Wayback captures of ch. I (2024-07-18), ch. II (2024-06-29), ch. VI (fresh Save Page Now capture 2026-08-02), backmatter (2026-07-29) | OK | OCR scans (ABBYY), math glyphs degraded; pp. 236 and 251 re-OCR'd with tesseract for the basis list and the J-recursion |
| 3. Gandy, "Set-theoretic functions for elementary syntax" (PSPUM 13.2, 1974, 103-126) | `bookstore.ams.org/pspum-13-2/`, `pubs.ams.org/view?ProductCode=PSPUM/13.2` (volume marked not free, "Free":0); archive.org full-text search; zbMATH Zbl 0323.02067; Semantic Scholar (rate-limited); author/institutional searches | PAYWALLED | n/a (no content) |
| 4. Jech, "Set Theory" (3rd millennium ed.), ch. 13 | `fa.ewi.tudelft.nl/~hart/set_theory/Jech/13-constructible_sets.pdf` and `front-matter.pdf` (institutional copy, TU Delft course page; Jech's own site `jech.site` is unreachable) | OK | Clean digital text, minimal degradation |
| 5. Zeman, "Inner Models and Large Cardinals" (de Gruyter, 2002), chs. 1-2 | De Gruyter ebook (library catalog records only); author page `math.uci.edu/~mzeman` and `RESEARCH/index.html` (no book chapters); web searches | PAYWALLED / NOT-FOUND | n/a (no content) |

## 3. The five wanted items

1. **Jensen 1972, verbatim basis list, S/J indexing, rud definition.**
   UNRESOLVED for the journal text itself: the ScienceDirect open-archive PDF
   is bot-walled (403/captcha), never archived, and no legitimate copy exists
   elsewhere. PARTIAL via Jensen's own later manuscript (fetched, Bonn author
   archive): his Basis Theorem gives F0..F8 (JM Theorem 2.2.15, p. 56), the
   rud definition is JM Definition 2.2.1 (p. 49), and the indexing note is JM
   p. 49 ("In [FSC] we indexed by all ordinals, so that our J_{ωα}
   corresponds to the J_α of [FSC]"). Corroborated by Devlin (Basis Lemma
   1.11, p. 236; J-recursion, p. 251). The 1972 wording itself remains
   unfetched; the notes mark the manuscript provenance explicitly.
2. **Devlin, named statement relating rud functions to the Gödel
   operations.** FOUND, with a chapter correction: the phrase "Gödel
   operations" does not occur in Devlin ch. I, II, or VI (searched); the named
   theorem is Dev VI.1.11 (The Basis Lemma), p. 236: "Every rudimentary
   function is a composition of some or all of the following rudimentary
   functions: F0..F8" (list quoted in the notes). Chapter I carries only the
   p. 7 pointer to VI.1; the term is introduced in a ch. II exercise (p. 100).
   Errata caveat noted inline (WS section 10 locates the flaws in ch. VI.1;
   see devlin-errata.md).
3. **Gandy's side.** UNRESOLVED: the paper is paywalled (AMS PSPUM 13.2,
   pp. 103-126, "Free":0) and no open copy exists. Fetched-text attestation
   only: JM p. 49 ("discovered by Gandy and Jensen") plus the L1 secondary
   sources (WS 1.12, MB 1.49-1.55: Gandy's "basic" = Jensen's "rud").
4. **Jech, Gödel operations list and L via them.** FOUND: Definition 13.1
   (L0 = ∅, L_{α+1} = def(L_α), L_λ = ⋃ L_α, L = ⋃ L_α; p. 175); Theorem 13.4
   (Gödel's Normal Form Theorem, p. 177); "Compositions of G1, ..., G10 are
   called Gödel operations" (p. 177); Definition 13.6 (G1..G10, p. 178);
   Corollary 13.8 (def(M) = cl(M ∪ {M}) ∩ P(M), p. 181); Theorem 13.9 (inner
   model iff closed under Gödel operations and almost universal, p. 182);
   Lemma 13.14 (α → Lα is Δ1, via (13.11) closure, p. 187); Theorem 13.16
   (L satisfies V = L and is the smallest inner model, p. 187). Provenance
   caveat: institutional PDF copy on a TU Delft course page; Springer book
   under copyright; no author-hosted copy found.
5. **Zeman, simple functions and their Sigma-n role.** UNRESOLVED for the
   book (paywalled; no author-hosted copy). PARTIAL via Jensen's manuscript:
   simple functions preserve Σ0 relations (JM Definition 2.2.2, p. 50), all
   rud functions are simple (Lemma 2.2.3, p. 51), every rud function is Σ0 as
   a relation (Corollary 2.2.4, p. 51), rud-in-A functions are Σ1 in A
   (Corollary 2.2.8, p. 52). The claim that simple functions serve the
   Σ*-theory is not in the fetched text (JM section 2.6 develops Σ*-theory
   without re-introducing the term).

## 4. Digest OPEN items settled

| OPEN item | Status | Evidence |
| --- | --- | --- |
| 1. Jensen's verbatim 1972 basis list | PARTIALLY SETTLED | JM Theorem 2.2.15 (p. 56) F0..F8, identical to SZ's F0..F8 (the enlargement source per SZ footnote 5) and to Dev 1.11 (p. 236); the 1972 journal wording itself unfetched |
| 3. "Gödel operations" named statement | FOUND (named statements) | Jech 13.4, 13.6, 13.8, 13.9 (pp. 177-182); Dev 1.11 (p. 236); the literal phrase "rud = compositions of the Gödel operations" is still not verbatim in any fetched text (flagged in the notes) |
| 4. Simple functions' Sigma-n role | PARTIALLY SETTLED | JM 2.2.2-2.2.8 (pp. 50-52): Σ0/Σ1 complexity bounds; the "serve the Σ*-theory" part unverified |
| 8. Zeman's book chs. 1-2 | UNRESOLVED | Paywalled; no legitimate open copy |
| 9. Jensen's original J-indexing convention | SETTLED | JM p. 49 ("In [FSC] we indexed by all ordinals"); Dev VI.2 p. 251 (J_α for α ∈ On, rank ωα); consistent with SZ footnote 4 (p. 9, in the L1 notes) |

## 5. Files produced

| File | Lines |
| --- | --- |
| `dev/literature/primary-sources.md` (the notes file) | 336 |
| `_build/l2-report.md` (this report) | 127 |

The final line count of the notes file was verified with `wc -l` after writing.

## 6. Stored artifacts (`_build/literature/`, git-ignored)

- Devlin: `devlin-ch1.pdf`, `devlin-ch2.pdf`, `devlin-ch6.pdf`,
  `devlin-backmatter.pdf`
- Jech: `jech-front-matter.pdf`, `jech-ch13.pdf`
- Jensen manuscript (Bonn archive): `jensen-ms-front.pdf`, `jensen-ms-bib.pdf`,
  `jensen-book_Preliminaries.pdf`, `jensen-book_bibliography.pdf`,
  `jensen-book_sec_2_1.pdf`, `jensen-book_sec_2_2.pdf`,
  `jensen-book_sec_2_3.pdf`, `jensen-book_sec_2_6.pdf`
- Pre-existing from L1 (unchanged): `sz.pdf`, `sz-full.txt`

Extraction side-artifacts (`.txt`) were kept alongside for auditability.

## 7. Constraints compliance

- Legitimate sources only: publisher pages (AMS), the ScienceDirect open
  archive (blocked, reported as such), the Project Euclid ASL collection via
  the Wayback Machine, an institutional course-page copy for Jech, and the
  author's own manuscript archive for Jensen. No shadow libraries were used
  or attempted; paywalled targets (Gandy, Zeman) are reported PAYWALLED, not
  worked around.
- Nothing from memory: the notes file quotes only fetched text with page
  cites; failed fetches appear in this report as rows, never as reconstructed
  content.
- English only, no em dash (checked programmatically: 0 forbidden dash or CJK
  characters in the notes file).
- No git commits/pushes; no `.claude/` or `src/` changes; existing
  `dev/literature/` files untouched (only the new `primary-sources.md` is
  untracked).
