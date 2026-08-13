# x1 report: extraction of the SZ fine-structure sections

Pass `x1` over `_build/literature/sz.pdf` (Schindler-Zeman, "Fine structure",
Handbook of Set Theory preprint, 58 PDF pages; chapter body = internal pages
5-58, cited as SZ p. N). Deliverable: `dev/literature/fine-structure.md`.
Intermediate extraction kept at `_build/literature/sz-full.txt` (pdftotext
-layout, full PDF), as the scope allows; nothing else was touched (not
digest.md, not the other collection files, not src/).

## Sections and pages extracted

- Chapter-level passages: p. 5 (intro, Σ* exclusion), p. 8 (Lemma 1.4 and the
  "simple" definition, for item 4), p. 14 (the reduction program, end of the
  proof of Theorem 1.15).
- Section 2, The first projectum: pp. 19-21 (Definitions 2.1, 2.5, 2.6, 2.8;
  Lemmata 2.2, 2.3, 2.7, 2.9; Corollary 2.4).
- Section 3, Downward extension of embeddings: pp. 21-25 (Lemmata 3.1-3.3 and
  proofs).
- Section 4, Upward extension of embeddings: pp. 25-32 (Definitions 4.1,
  Lemma 4.2 and proof; footnote 7 on "lightface", p. 31).
- Section 5, Iterated projecta: pp. 32-36 (Definitions 5.1, 5.2, 5.7, 5.12;
  Lemmata 5.3-5.6, 5.8-5.11, 5.13; the Σ_ℓ^{(n)}/Σ* passage).
- Section 6, Standard parameters: pp. 36-39 (Definitions 6.1, 6.3, 6.6;
  Lemmata 6.2, 6.4-6.8).
- Section 7, Solidity witnesses: pp. 39-42 (Definitions 7.1, 7.3, 7.5, 7.10,
  7.13; Lemmata 7.2, 7.4, 7.6-7.12; nth core remark).
- Section 8, Fine ultrapowers: pp. 42-52 (Definitions 8.1, 8.3, 8.5, 8.6,
  8.9, 8.11; Theorems 8.2, 8.4, 8.7, 8.10; Lemmata 8.8, 8.12, 8.14;
  Corollary 8.13).
- Section 9, Applications to L: pp. 52-56 (Lemmata 9.1-9.2 with proofs,
  Theorems 9.3, 9.5, Corollary 9.4).
- Bibliography: p. 57 (entries [14], [15]).

Page numbers were verified per page against the PDF's running heads
(PDF page N = internal page N throughout the chapter) and against
`pdftotext -f N -l N` spot checks for every quoted item.

## Answer status for the six extraction items

1. Projecta: FOUND. Definition 2.1 (SZ p. 19) verbatim: ρ(M) = the least
   ρ ∈ On such that P(ρ) ∩ Σ_1^M ⊄ M. Alternative characterizations: Lemmata
   2.2-2.3 and Corollary 2.4 (p. 19, ρ(M) a cardinal in M when in M; ρ a
   Σ1-cardinal; |J_ρ^A| = H_ρ^M and amenability of ⟨J_ρ^A, B⟩), Definition
   5.1 with ρ_ω (p. 32), Lemma 5.3(c) (p. 33: ρ(M^{n,p}) = ρ_{n+1}(M) for p ∈
   R_M^n), and the ρ_2 caveat for non-1-sound M (p. 32).
2. Standard codes: FOUND. Definition 2.5 (p. 20) verbatim: A_M^p = {⟨i, x⟩ ∈
   ω × H_ρ^M ; M ⊨ ϕ_i(x, p)}, the reduct M^p = ⟨J_ρ^B, A_M^p⟩, and the
   restricted A_M^{p,δ}, M^{p,δ}; iteration in Definition 5.1 (p. 32);
   standard parameter p_n(M), standard reduct M^n (Definition 6.3, p. 37);
   standard parameter p(M) (Definition 6.6, p. 37). Terminology: SZ never say
   "master code" (zero occurrences); the digest's "A^n" maps to SZ's
   A_M^{n,p_n(M)}.
3. Reduction theorems: FOUND in SZ's exact form, with a terminology caveat.
   The load-bearing statements are Lemma 5.6 (p. 34, verbatim): A ⊆ M^{n,p}
   Σ_{n+1}^M implies A is Σ_1^{M^{n,p}}, for p ∈ R_M^n; Lemma 5.5 (p. 34):
   Σ_ω^M ∩ P(M^{n,p}) = Σ_ω^{M^{n,p}}; Lemma 5.9 (p. 35): π : M̄^{n,p̄}
   →_{Σ_ℓ} M^{n,p} extends to π̃_0 : M̄ →_{Σ_{ℓ+n}} M. The chapter states the
   program in words on p. 14 ("under favourable circumstances Σn over M can
   be viewed as Σ1 over a 'reduct' of M"). SZ do NOT state a literal
   one-line "Σ_n over J_α = Σ_1 over (J_{ρ_n}, A_n)" theorem; the exact
   hypotheses are acceptability + a very good parameter, with soundness
   (Definition 5.7, p. 34; Lemma 6.8, p. 37; Lemma 9.2, p. 52) required for
   the standard-parameter version.
4. Simple functions: NOT IN CHAPTER beyond Lemma 1.4's proof. The term
   "simple" is defined only on p. 8 (inside the proof of Lemma 1.4); its
   other occurrences are prose (pp. 27, 36, 52). No Σ_n-preservation role is
   claimed anywhere in the chapter. Digest OPEN item 4 is therefore settled
   for SZ; the claimed role, if real, would have to come from [15]/[14]
   (cite-only here).
5. Sigma-star machinery: NOT IN CHAPTER (explicitly excluded). Verbatim
   exclusion on p. 5 (points to [15, Sections 1.6-1.8] or [14]); the only
   substantive mention is p. 36 (the Σ_ℓ^{(n)}-formulae "lead towards"
   Jensen's Σ*, "dealt with in [15, Sections 1.6 ff.]"). What SZ use instead:
   rΣ_{n+1} elementary maps (Definition 5.12, p. 36, following [8, §2]) and
   n-embeddings (Definition 7.13, p. 42).
6. Dependencies: FOUND (dependency list in the deliverable, section 6):
   acceptability as a standing hypothesis; rud_A-closedness + amenability of
   M (explicit at pp. 44, 45); amenability of the reduct via Corollary 2.4(a)
   (p. 19); the Lemma 1.4 hypothesis A ∩ V^{rk(U)+ω} ⊆ U with SZ's "always
   met in the construction of fine structural inner models" (p. 8); the
   Σ1-satisfaction/Skolem theorems (1.14-1.15, p. 13) and Lemma 1.17 (p. 15);
   very good parameters presupposed (p. 36); Q-formulae used only in section 1
   (pp. 15-17); soundness/solidity for the ultrapower theorems (pp. 48-49).

## Headline: how the master-code question came out

The reduction is present in the chapter and is now pinned verbatim, but it is
not called "master codes" and it is not parameter-free. The exact theorem is
SZ Lemma 5.6 (p. 34): for acceptable M and p ∈ R_M^n, every Σ_{n+1}^M subset
of the n-th reduct M^{n,p} is Σ_1^{M^{n,p}}. The embedding-extension form is
Lemma 5.9 (p. 35): a Σ_ℓ embedding between n-th reducts lifts (n-completion)
to a Σ_{ℓ+n} embedding of the full structures. The chapter's own one-sentence
summary is p. 14: "Jensen solved this problem by showing that under
favourable circumstances Σn over M can be viewed as Σ1 over a 'reduct' of M."
The "favourable circumstances" are: an acceptable structure, a very good
parameter; and when the parameter must be the standard one, soundness
(Definitions 2.8 p. 21, 5.2 p. 32, 5.7 p. 34; Lemma 6.8 p. 37; J_α sound for
limit α, Lemma 9.2 p. 52). The digest's OPEN item 5 is resolved in this exact
form; the digest's term "master code" and the notation A^n should be
reconciled to SZ's "standard code" A_M^{n,p} and n-th reduct M^{n,p}
(deliverable sections 2-3).

## Consistency with the existing collection files

- No contradictions found. The previously collected items cited by
  j-hierarchy.md (Theorems 1.14-1.17, Definition 1.20, Corollary 1.22, Lemmata
  9.1-9.2 on p. 52, the zig-zag wording) were re-verified in this pass and
  agree page-for-page.
- digest.md OPEN item 4 ("Simple functions' Sigma-n role") is now settled for
  the SZ chapter: NOT IN CHAPTER (see status item 4); the item remains open
  only for Zeman's book [15] and Welch's chapter [14], both cite-only.
- digest.md OPEN item 5 ("The master-code reduction") is now settled in SZ's
  own form (Lemma 5.6 + Lemma 5.9 + the p. 14 summary); one wording note:
  "master code" is not SZ terminology, and the digest's "(J_{ρ_n}, A_n)"
  shorthand is not a verbatim SZ statement.
- digest.md section 4, item 2 flagged that "simple functions preserve
  Sigma-n definability and serve the Sigma-star theory" is NOT in the fetched
  text; this pass confirms that flag for the entire SZ chapter.
- One page-precision note for the record: the "reduct" program sentence is on
  SZ p. 14 (end of the proof of Theorem 1.15), i.e. the proof of 1.15 runs
  over pp. 13-14; j-hierarchy.md's citation of Theorem 1.15 at p. 13 remains
  correct for its statement.

## Deliverable facts

- File: dev/literature/fine-structure.md
- Line count: 579 lines
- DEGRADED markers: 6 spots, all restorations forced by context and flagged in
  the deliverable's section 8 (Definition 5.1 layout, the stray "S" glyph in
  the p. 32 remark, the h-function domain exponents, the Lemma 3.1 arrow
  subscripts, the Σ_ℓ^{(n)}/rΣ_{n+1} sub/superscripts, and the dotted-language
  symbols in the Lemma 1.4 quote).
- OPEN items carried forward: the content of Σ* itself and any simple-function
  role in it ([15, Sections 1.6 ff.] / [14], both cite-only); whether Zeman's
  book states the reduction in the digest's literal "(J_{ρ_n}, A_n)" form.
