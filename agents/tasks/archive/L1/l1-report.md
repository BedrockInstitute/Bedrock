# L1 report: classified literature collection for the rud route

Date: 2026-08-02. Scope: fetch the open sources of the raw sweep, extract
load-bearing content with per-claim citations, and answer Q1-Q7. Deliverables
under dev/literature/ plus this report. No git mutations were performed.

## 1. Network status

Network self-test: `curl -sI https://arxiv.org | head -3` returned HTTP/2 200.
Network available; all fetches below were attempted.

## 2. Per-source fetch results

Legend: OK = full content fetched and extracted; DEGRADED = content fetched but
text extraction loses math glyphs or the content is a draft; FAILED = full text
not obtainable (with fallback used, if any); CITE-ONLY = no fetch attempted.

| # | Source | Result | Notes |
| --- | --- | --- | --- |
| 1 | Mathias & Bowler, NDJFL 56(1), 2015 (preprint hbm613.pdf) | OK, DEGRADED (glyphs) | 40 pp. PDF fetched; pdftotext degrades union/member-of/Delta glyphs (union as S, member-of as 2, Delta_0 as 0); quotes restored where unambiguous |
| 2 | Mathias, Weak systems (pr614.pdf) | OK, DEGRADED (glyphs) | 76 pp. fetched; same glyph degradation |
| 3 | Schindler & Zeman, Fine structure (finestructure.pdf) | OK, DEGRADED (glyphs) | 58 pp. fetched; server TLS certificate broken, fetched with -k; same glyph degradation |
| 4 | Stanley, JSL review of Devlin | FAILED (paywalled) | Project Euclid and JSTOR both bot-protected live; full text is subscriber-only. Metadata fetched via Wayback (JSL 52(3), 1987, 864-867; DOI 10.2307/2274371). Error content taken from Mathias WS section 10 and the Welch draft, explicitly attributed |
| 5 | Mathias, Freiburg slides | OK, DEGRADED (glyphs) | 59 slides fetched; same glyph degradation |
| 6 | "Weak set theories in foundational debates", Phil. Trans. R. Soc. A | FAILED (not open access; bot-protected) | Publisher page Cloudflare-blocked; Unpaywall is_oa=false; Europe PMC subscription required. Abstract fetched from PubMed (PMID 37031698) and used for the role line only |
| 7 | Paulson, AC in Isabelle/ZF | OK | arXiv abs page + 67 pp. PDF + 202 pp. library outline + 19 slides all fetched; minimal glyph loss |
| 8 | Flypitch CPP 2020 | OK | 14 pp. PDF fetched; minimal glyph loss |
| 9 | Flypitch ITP 2019 | OK | 19 pp. PDF fetched; minimal glyph loss |
| 10 | Flypitch GitHub | OK | README fetched from github.com/flypitch/flypitch |
| 11 | Welch, "Syntax without arithmetic or concatenation" (extra) | OK, DEGRADED (draft + glyphs) | 4 pp. draft (Oct 10 2012) fetched; text heavily symbol-degraded; treated as secondary only |
| 12 | MathOverflow 77734 (extra) | OK | Question body fetched via StackExchange API; corroborates Stanley-review point only |
| 13 | Cite-only sources 9-14 of the sweep (Jensen 1972, Devlin, Zeman, Gandy, Kunen, Jech, Schindler book), plus Jensen-Karp 1971 added from MB's bibliography | CITE-ONLY | Citations recorded in BIBLIOGRAPHY.md; no fetching |

Degradation note (all PDFs): pdftotext output was used. Mathematical symbols
(union, member-of, Delta_0, Sigma_1, etc.) are frequently lost or mapped to
ASCII letters. Quotes in the notes restore the intended symbol where the
context makes it unambiguous; nothing was silently reworded.

## 3. Files produced (line counts)

Counts are of the final files as written (wc -l).

| File | Lines |
| --- | --- |
| dev/literature/rudimentary-functions.md | 465 |
| dev/literature/j-hierarchy.md | 204 |
| dev/literature/devlin-errata.md | 266 |
| dev/literature/formalizations.md | 243 |
| dev/literature/BIBLIOGRAPHY.md | 192 |
| _build/l1-report.md | 247 |

The directory also contains dev/literature/owner-notes-rud.md (committed by the
owner as 8781bfa). It is the owner's reference note, outside the scope of this
task ("create files only under dev/literature/"); it was read once to identify
it and left unmodified, and it was NOT used as a source (the rules require
fetched text or the raw sweep).

## 4. UNVERIFIED marks and their reasons

1. Jensen's original rud list (Q1). Not reproduced verbatim in any fetched
   text. What is verifiable: SZ footnote 5 states the F0..F15 list is an
   enlargement of the list from [3, Lemma 1.8] (Jensen 1972); the F0..F15 list
   itself is quoted (SZ p. 10). The exact original list = not determinable
   from fetched material.
2. "Minimal model J_omega" phrasing (sweep's role line for Mathias-Bowler).
   The phrase is not in the fetched MB text. Nearest fetched statements: Fr
   slide 28 "Jω is provident. The next one will be Jω2."; MB 5.9 "The first
   Jensen fragment after J1 that is closed under functions of Type II is Jω".
   The sweep's exact phrasing = not determinable from fetched material.
3. Stanley's review wording (Q6). The review full text is paywalled and was
   not fetched. All "per Stanley" content in devlin-errata.md comes from
   Mathias's account (WS section 10) or the Welch draft (p. 1), and is
   attributed as such. Any claim about the review's own wording = UNVERIFIED.
4. Paulson section 2.7 vs Conclusions on GCH/♦ (Q7). P p. 11 says "We prove
   ZFL ` AC, ZFL ` GCH and ZFL ` ♦", but P Conclusions (p. 65), PS slide 19,
   and the PI outline theory graph (no GCH theory) all indicate GCH/♦ were
   NOT mechanized. Which reading of the section 2.7 sentence is intended =
   UNVERIFIED; the artifact evidence (outline, slides, conclusions) is
   consistent with "not formalized".
5. Mizar / Metamath / Naproche status (Q7). No fetched text mentions any of
   them as set-theory developments (PS slide 1 mentions "thousands of Mizar
   proofs" only as a count). Not determinable from fetched material.
6. "Is ANY rud-based development formalized anywhere?" (Q7). No fetched source
   reports one. Not determinable from fetched material (absence of mention,
   not a proof of absence).

## 5. Answers to Q1-Q7 (with cites)

### Q1. The exact contemporary rud basis, function by function

- Schindler-Zeman use six schemata (SZ Def. 1.1, p. 6): projection f(<x1..xk>)
  = xi; set difference xi \ xj; unordered pair {xi, xj}; tuple/composition
  <g1(...), ..., g_l(...)>; bounded union union_{y∈x1} g(<y,x2..xk>); and for
  rud_A the schema f(x) = x ∩ A. Rud = rud_empty (no A-schema).
- SZ's finite basis for the S-hierarchy is F0..F15 (SZ p. 10): {x,y}; x\y;
  x×y; {<u,z,v> ; z∈x ∧ <u,v>∈y}; {<u,v,z> ; z∈x ∧ <u,v>∈y}; union x; dom(x);
  ∈∩(x×x); {x"{z} ; z∈y}; <x,y>; x"{y}; <left(y),x,right(y)>;
  <left(y),right(y),x>; {left(y),<right(y),x>}; {left(y),<x,right(y)>}; A∩x.
  Stated to be "a basis for the set of rud_A functions (cf. [3, Lemma 1.8])",
  with footnote 5: the list contains more functions than [3]'s, to make S^A_α
  transitive.
- Mathias's corrected list (MB section 2, p. 13; WS 2.61, pp. 19-20): R0 =
  {x,y}; R1 = x\y; R2 = union x; R3 = Dom(x); R4 = x×y; R5 = x ∩ {(a,b)2 |
  a∈b}; R6 = {(b,a,c)3 | (a,b,c)3∈x}; R7 = {(b,c,a)3 | (a,b,c)3∈x}; R8 =
  {x"{w} | w∈y}. B (basic) = closure of R0..R7; R (rudimentary) = closure of
  R0..R8 (MB 2.0).
- The "extra" function beyond the Devlin Basic generators: R8, because GJ0 =
  DB0 + R8 (WS 1.12, p. 11; MB 1.49-1.54). Transitive sets closed under R are
  exactly the models of GJ0 (WS 2.85, p. 23).
- Jensen's original list: see UNVERIFIED 1.

### Q2. S vs J hierarchy, condensation, well-order, acceptability

- J-hierarchy: J_0^A = ∅; J_{α+ω}^A = rud_A(J_α^A ∪ {J_α^A}); J_{ωλ}^A =
  union_{α<λ} J_{ωα}^A for limit λ; L[A] = union J_{ωα}^A (SZ Def. 1.6,
  p. 9). Indexed by limit ordinals "for later purposes", "in contrast with
  [3]" (SZ footnote 4, p. 9).
- S-hierarchy: S_0^A = ∅; S_{α+1}^A = S^A(S_α^A); S_λ^A = union S_ξ^A for
  limit λ, where S^A(U) = union_{i=0}^{15} F_i"(U ∪ {U})^2 (SZ p. 9-10).
  J_α^A = S_α^A for all limit α (I.1); finite rank jump per step; J_α^A ∩ On
  = α (SZ p. 10). MB: Jν = T_{ων} (MB 0.3, p. 2; Fr slide 14), and ν -> ων is
  not rud rec (Fr slide 14).
- Condensation: at the Sigma_1 level. "Let M = <J_α^A, B> be a J-structure,
  and let π : M̄ ->_Σ1 M where M̄ is transitive. Then M̄ is a J-structure"
  (SZ Thm. 1.16, p. 14). Preservation of acceptability: downward under Σ1
  embeddings, upward under Q-embeddings (SZ Cor. 1.22, p. 17).
- Canonical well-order: recursive definition on S_β^A; limit stages union the
  previous orders; successor stage β = β̄+1 compares (a) both in S_{β̄}^A by
  the old order, (b) new vs old stage membership, (c) the <^A_{β̄,lex}-minimal
  producer triple (i, u_x, v_x) with x = F_i(u_x, v_x) (SZ p. 11). The
  sequence h<^A_γ ; γ<αi is uniformly Σ1^{J_α^A} (SZ Lemma 1.11, p. 11);
  otp(<^A_α) = α when α is closed under the Gödel pairing function (SZ Lemma
  1.17, p. 15).
- Acceptability: P(τ) ∩ J_{ξ+ω}^A ⊄ J_ξ^A for τ < ξ implies a surjection f :
  τ -> ξ in J_{ξ+ω}^A (SZ Def. 1.20, p. 16); "can be considered as a strong
  version of GCH" (SZ p. 16); acceptability is a Q-property (SZ Lemma 1.21,
  pp. 16-17). Jα is acceptable and sound for every limit α (SZ 9.1-9.2,
  p. 52).

### Q3. The comprehension theorem

- SZ Lemma 1.4 (p. 8): for U transitive and A with A ∩ V^{rk(U)+ω} ⊆ U,
  P(U) ∩ rud_A(U ∪ {U}) = P(U) ∩ Σ_ω^{<U,∈,A>}. Proof: one page, two
  inductions ("⊇" via closure of rud relations under complement/intersection/
  bounded quantification, Prop. 1.3; "⊆" via "simple" functions). Corollaries:
  Σ0 comprehension in rud-closed transitive sets (1.5, p. 8); amenability of
  <J_α^A, B> for B ∈ Σ0^{J_α^A} (1.8, p. 10).
- MB version: Bernays theorem, all Δ0 separation in DB0 (MB 1.43, p. 11);
  separators x -> x ∩ A ∈ B (MB 2.1, p. 13); the heavy work moved to the truth
  predicate: "Truth for Δ̇0 sentences is uniformly Δ1 for transitive models of
  MW" (MB 9.0, p. 37), a 4-step proof (de-nesting, prenex, evaluation via
  addition attempts, tree of substitution instances), and |=u φ is Δ^MW_1
  (MB 9.2, p. 38).
- Welch draft (extra, secondary): the term-simulation route with explicit
  code trees and a recursive map k, giving R ⊢ φ ⇐⇒ GJ ⊢ φ and finite
  axiomatizability of GJ (W Thm. 2 and Lemmas 7, 10, pp. 7-10). DRAFT.
- Length/structure: SZ is the shortest (Lemma 1.4, 1 page, no syntax
  machinery); MB is about 1.5 pages in section 9 plus the companion theory of
  attempts at addition; W spells out the syntactic simulation in about 2 pages.

### Q4. The canonical <_J construction

As in Q2: stage-first (older stages precede), then within a new stage the
lexicographic order on the minimal producer triple (i, u, v) with x = F_i(u,v)
over 16 × S^A_{β̄} × S^A_{β̄} (SZ p. 11). Uniformly Σ1 over J_α^A (SZ 1.11,
p. 11). Used for the surjection g : α -> J_α^A when α is Gödel-pairing closed
(SZ 1.17, p. 15).

### Q5. Relativization rud_A

One added schema, x -> x ∩ A, in SZ's Def. 1.1 (p. 6); equivalently F15 =
A ∩ x in the finite basis (SZ p. 10). Membership in A is rud_A (SZ 1.3(d),
p. 7); P(U) ∩ rud_A(U ∪ {U}) = P(U) ∩ Σ_ω^{<U,∈,A>} (SZ 1.4, p. 8). The
unrelativized basis R0..R8 has no A-function; the Welch draft adds f_{17+i} =
A_i ∩ x for predicates (W Def. 5, p. 6, secondary). Zeman's own book was not
fetched (cite-only).

### Q6. What broke in Devlin (do-not-repeat checklist)

Full checklist in devlin-errata.md. Headline classes (all from WS section 10,
pp. 56-66, unless noted):

1. False Δ0 claims for syntax: F∧ ("Dom(θ) = Dom(φ) + Dom(ψ) + 3" needs
   addition), hence Build, Seq, and Sat lemmas fail; F∧ is Δ^BS_1 not Δ0
   (WS Lemma 9.3, 10.3; Lemma 9.4, 10.4; 9.5 false; 9.10 Sat false and
   uncurable in BS).
2. Unbounded finite-sequence claims: BS proves [ω]^1, [ω]^2 but not [ω]^3
   (MB 1.46, p. 11), so S_ϑ cannot be formed and |= cannot be defined.
3. Levels-of-language ambiguity: the two definitions of "Σ0 function" (class
   term vs pointwise with transitive M) are only equivalent under TCo
   (WS 10.0-10.1).
4. Uniformity of truth over amenable sets fails; needs S-amenability
   (WS pp. 62-63, 10.12).
5. Proof reuse of the false 9.3 taints VI.1.14 (WS p. 64); the correct Δ0
   truth result is MB 9.0-9.2.
6. Slips: Finseq domain; 'n' for 'm' in A(x); G∃ arity; F∈ vs F∃; 1.7 vs
   1.8; citation volume of the Stanley review (52 not 53).
7. TCo error: "the transitive closure of any set exists" is not provable even
   in Zermelo set theory, despite a claim in Devlin (SZ footnote 3, p. 9;
   model in WS section 12).

Stanley's role: per Mathias, Stanley's review drew attention to the flaws
(WS p. 56); per Welch, Stanley suggested BS augmented with the rudimentary
functions as a cure, i.e. GJ + infinity (W p. 1). Review full text itself
UNVERIFIED (see section 4.3).

### Q7. Formalization landscape

- Paulson: relative consistency of AC formalized in Isabelle/ZF via
  satisfaction internalization following Kunen (P sections 2, 6; DPow matched
  to Kunen's Definition VI 1.1, P p. 32). Verdict: "unusually long, and not
  entirely satisfactory: two parts of the proof do not fit together"
  (P abstract, p. 1); comprehension scheme not proved schematically, about 35
  instances proved separately (P p. 65; PS slide 15 says 40, discrepancy
  noted); the V=L-in-L proof cannot be combined with V=L => AC (P p. 65).
  GCH: NOT formalized; "Future investigators might also try formalizing the
  proof that L satisfies the generalized continuum hypothesis and the
  combinatorial principle ♦" (P p. 65); "Prove generalized continuum
  hypothesis" is a future challenge (PS slide 19); no GCH theory in the
  outline (PI p. 8). Section 2.7 discrepancy flagged (UNVERIFIED 4).
- Flypitch: independence of CH in Lean 3, both directions, via Boolean-valued
  models: Cohen forcing for ¬CH, σ-closed collapse forcing for CH (FC
  abstract, p. 1); deep embedding of FOL with a Boolean-valued soundness
  theorem; theorem independence_of_CH : independent ZFC CH_f (FG README).
  ITP 2019 covers only the ¬CH direction (regular opens of 2^ω; FI abstract).
  Constructible universe: NOT constructed; "Consistency of CH via construction
  of the constructible universe" is listed as possible future work (FG
  README). Models are bSet B, the Aczel encoding of set theory (FC p. 2-3).
- Anything else: only FC's related-work line mentions other formalization:
  Gunther, Pagano, Terraf "first steps towards formalizing forcing, by way of
  generic extensions of countable transitive models" (FC p. 4). Mizar,
  Metamath, Naproche: not determinable from fetched material (UNVERIFIED 5).
- GCH-in-L: virgin territory relative to the fetched documents (both Paulson
  and Flypitch list it as future work). Any rud-based formalization: nothing
  found in the fetched material (UNVERIFIED 6).

## 6. Compliance notes

- English only; no em dashes in the notes (checked by construction; the only
  fetched text containing em dashes is inside quotes normalized to commas or
  hyphen forms, per repo rules).
- No git mutations were performed (no commits, no staging). Read-only git
  queries (status, check-ignore, log, ls-files) were used only to identify the
  pre-existing owner file and to confirm the task made no other changes.
- Generated files: none committed; _build/l1-report.md and dev/literature/*
  are the only outputs of this task.
- dev/literature/owner-notes-rud.md was left untouched.
