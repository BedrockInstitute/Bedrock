# Fine structure: projecta, standard codes, the reductions, and their dependencies

Developer notes for the rud-route formalization. Extraction pass `x1`
(2026-08-02) over the fetched SZ preprint, targeted at the fine-structure
sections after the material already collected in `j-hierarchy.md` (through
Definition 1.20 / Lemmata 1.21-1.27) and `rudimentary-functions.md` (through
Lemma 1.4 and the S-hierarchy). Primary source: SZ = Schindler & Zeman, "Fine
structure", Handbook of Set Theory (author preprint; PDF internal pages 5-58,
cited below as SZ p. N). Full citations in BIBLIOGRAPHY.md.

Sections extracted: 2. The first projectum (pp. 19-21), 3. Downward extension
of embeddings (pp. 21-25), 4. Upward extension of embeddings (pp. 25-32),
5. Iterated projecta (pp. 32-36), 6. Standard parameters (pp. 36-39),
7. Solidity witnesses (pp. 39-42), 8. Fine ultrapowers (pp. 42-52),
9. Applications to L (pp. 52-56), plus the chapter-level passages on pp. 5, 14
and the bibliography (p. 57).

Extraction note: pdftotext degrades math glyphs and loses
subscript/superscript positions (union as S, member-of as 2, Delta/Sigma
sub/superscripts as line artifacts, 6-subset as "6⊆"). Quotes below restore
the intended symbols where unambiguous, following the convention of the other
collection files; spots where restoration is less than fully confident are
marked DEGRADED. All page numbers were re-verified against the running heads
of the PDF (PDF page N = internal page N for the chapter pages).

## 1. The projecta (digest OPEN item 5, first half)

SZ's own framing of what a projectum is (SZ p. 19, section 2 opening),
verbatim (symbols restored; the source's dash rendered as a colon):

> We now introduce the central notions of fine structure theory: the notions
> projectum, standard code and good parameter. We stress that we are working
> with arbitrary J-structures and that these structures have, in general,
> very few closure properties. This means that there might be bounded
> definable subsets of these structures (in a precise sense) failing to be
> elements. However, each J-structure has an initial segment which is "firm"
> in the sense that it does contain all sets reasonably definable over the
> whole structure. The height of this "firm" segment is called the projectum.
> Standard codes are (boldface) definable relations computing truth and good
> parameters are parameters which occur in the definitions of standard codes.

Definition of the first projectum, verbatim (SZ Definition 2.1, p. 19;
"6⊆" restored to "⊄"):

> 2.1 Definition. The Σ1-projectum (or, first projectum) ρ(M) of an
> acceptable J-structure M = J_α^A is defined by
>
> ρ(M) = the least ρ ∈ On such that P(ρ) ∩ Σ_1^M ⊄ M.

Alternative characterizations SZ prove for the first projectum:

- SZ Lemma 2.2 (p. 19), verbatim: "Let M be as above. If ρ(M) ∈ M, then ρ(M)
  is a cardinal in M." Proof (p. 19): given f ∈ M with f : γ → ρ onto for
  γ < ρ and a = A ∩ ρ ∉ M with A ∈ Σ_1^M, the pullback ā = f^{-1}"a is ∉ M
  (else a = f"ā ∈ M), yet ā ∈ M by the defining minimality of ρ since
  ā ⊆ γ and ā ∈ Σ_1^M. Contradiction.
- SZ Lemma 2.3 (p. 19), verbatim: "Let M be as above and ρ = ρ(M). Then ρ is
  a Σ1-cardinal in M (i.e. there is no Σ_1^M partial map from some γ < ρ onto
  ρ)." The proof (p. 19) uses the Σ_1^M map of ρ onto J_ρ^A (Lemma 1.17) and
  a diagonal argument, then Lemma 1.23 for ρ ∈ M.
- SZ Corollary 2.4 (p. 19), verbatim: "Let M be acceptable and ρ = ρ(M).
  (a) If B ⊆ J_ρ^A is Σ_1^M, then ⟨J_ρ^A, B⟩ is amenable. (b) |J_ρ^A| =
  H_ρ^M." Stated to follow immediately from Lemmata 1.17 and 1.23.

Iterated projecta, verbatim (SZ Definition 5.1, p. 32; sub/superscript
positions restored; the "n,p" superscript on M in the min is restored from
the extraction artifact and confirmed by Lemma 5.3(c)):

> 5.1 Definition. Let M = ⟨J_β^B, D⟩ be an acceptable J-structure. For n < ω
> we recursively define the n-th projectum ρ_n(M), the n-th standard code
> A_M^{n,p} and the n-th reduct M^{n,p} as follows:
>
> ρ_0(M) = β,  Γ_M^0 = {∅},  A_M^{0,∅} = ∅,  M^{0,∅} = M,
> ρ_{n+1}(M) = min{ρ(M^{n,p}); p ∈ Γ_M^n},
> Γ_M^{n+1} = ∏_{i ∈ n+1} [ρ_{i+1}(M), ρ_i(M))^{<ω},
>
> and for p ∈ Γ_M^{n+1},
>
> A_M^{n+1,p} = A_{M^{n,p↾n}}^{p(n), ρ_{n+1}(M)}   and
> M^{n+1,p} = (M^{n,p↾n})^{p(n), ρ_{n+1}(M)}.
>
> We also set ρ_ω(M) = min{ρ_n(M); n < ω}. The ordinal ρ_ω(M) is called the
> ultimate projectum of M.

The remark after Definition 5.1 (SZ p. 32) is load-bearing for the digest's
item 5, verbatim:

> The reader will gladly verify that ρ_1(M) = ρ(M). On the other hand, if M
> is not 1-sound (cf. Definition 5.7 below) then it need not be the case that
> ρ_2(M) is the least ρ such that P(ρ) ∩ Σ_2^M ⊄ M.

So the naive "least ρ with a new Σ_n subset" characterization is explicitly
NOT valid at level n+1 for structures that fail to be n-sound. The next
sentence (SZ p. 32; DEGRADED, see section 8) identifies a parameter p ∈
Γ_M^{n+1} with its range when the projecta decrease:

> Supposing that we know ρ_n(M) ≤ ⋯ ≤ ρ_1(M) we may identify p = ⟨p(0), ...,
> p(n)⟩ ∈ Γ_M^{n+1} with the (finite) set ran(p) of ordinals; this will play
> a rôle in the next section.

Projecta and very good parameters: SZ Lemma 5.3 (p. 33), verbatim
(the fragment relevant here is (c)):

> 5.3 Lemma. Let M be acceptable.
> (a) R_M^n ⊆ P_M^n ≠ ∅
> (b) Let p ∈ R_M^n. If q ∈ Γ_M^n then A^{n,q} is rud_{M^{n,p}} in parameters
> from M^{n,p}.
> (c) Let p ∈ R_M^n. Then ρ(M^{n,p}) = ρ_{n+1}(M).
> (d) p ∈ P_M^n =⇒ ∀ i ∈ n p(i) ∈ P_M^{i,p↾i}, and similarly for R_M^n.
> Moreover, if p ↾ (n − 1) ∈ R_M^{n−1} then equivalence holds.

Application of the ultimate projectum in section 9 (SZ p. 52, proof of
Lemma 9.1, equation (I.31)): in the acceptable-J_β argument, the least τ < β
with a new subset a ⊆ τ at J_{β+ω} satisfies

> τ = ρ_ω(J_β).

## 2. Standard codes, reducts, and standard parameters (digest OPEN item 5,
second half)

The first-level standard code and reduct, verbatim (SZ Definition 2.5, p. 20;
symbols restored):

> 2.5 Definition. Let M = ⟨J_α^B, D⟩ be an acceptable J-structure, ρ = ρ(M)
> and p ∈ M. We define
>
> A_M^p = {⟨i, x⟩ ∈ ω × H_ρ^M ; M ⊨ ϕ_i(x, p)}.
>
> A_M^p is called the standard code determined by p. Let us stress that A_M^p
> is the intersection of ω × H_ρ^M with a set Ã_M^p (defined in an obvious
> way) which is Σ_1^M({p}). We shall often write A_M^p(i, x) instead of
> ⟨i, x⟩ ∈ A_M^p. The structure
>
> M^p = ⟨J_ρ^B, A_M^p⟩
>
> is called the reduct determined by p. If δ = ρ or δ < ρ where δ is a
> cardinal in M, we also set
>
> A_M^{p,δ} = A_M^p ∩ J_δ^B
> M^{p,δ} = ⟨J_δ^B, A_M^{p,δ}⟩.
>
> We shall omit the subscript M whenever there is no danger of confusion.

Good and very good parameters, verbatim (SZ Definitions 2.6 and 2.8, pp.
20-21):

> 2.6 Definition. Let M be acceptable and ρ = ρ(M).
> P_M = the set of all p ∈ [ρ(M), On ∩ M)^{<ω} for which there is a B ∈
> Σ_1^M({p}) such that B ∩ ρ ∉ M.
> The elements of P_M are called good parameters.

> 2.8 Definition. Let M be acceptable and ρ = ρ(M). We set
> R_M = the set of all r ∈ [ρ(M), On ∩ M)^{<ω} such that h_M(ρ ∪ {r}) = |M|.
> The elements of R_M are called very good parameters.

SZ Lemma 2.9 (p. 21): "R_M ⊆ P_M ≠ ∅." The remark after it (SZ p. 21),
verbatim:

> We remark that P_M and R_M are often defined differently so as to include
> arbitrary elements of M rather than just finite sequences of ordinals in
> the half-open interval [ρ(M), On ∩ M).

The n-th standard code and n-th reduct are the iterated objects of Definition
5.1 (quoted in section 1, p. 32). The good/very good parameter families
iterate too (SZ Definition 5.2, p. 32), verbatim:

> 5.2 Definition. We define P_M^n, R_M^n ⊆ Γ_M^n as follows:
> P_M^0 = {∅}
> P_M^{n+1} = {p ∈ Γ_M^{n+1}; p ↾ n ∈ P_M^n ∧ ρ(M^{n,p↾n}) = ρ_{n+1}(M) ∧
> p(n) ∈ P_{M^{n,p↾n}}}
> R_M^n is defined in the same way but with R_{M^{n,p↾n}} in place of
> P_{M^{n,p↾n}}.
>
> As before, we call the elements of P_M^n good parameters and the elements of
> R_M^n very good parameters.

Standard parameters and standard reducts, verbatim (SZ Definitions 6.3 and
6.6, p. 37; the <*-order is Definition 6.1, p. 36):

> 6.1 Definition. Let a, b ∈ [On]^{<ω}. Set
> a <* b ⇐⇒ ∃ α ∈ b (a \ (α + 1) = b \ (α + 1) ∧ α ∉ a).

with footnote 8 (SZ p. 36): "I.e., max(a△b) ∈ b." The commentary (SZ p. 36)
notes: "The ordering <* has a rudimentary definition, therefore it is
absolute for transitive rudimentarily closed structures and is also preserved
under embeddings which are Σ0 elementary. If we view finite sets of ordinals
as finite decreasing sequences, a <* b precisely when a precedes b
lexicographically." And Lemma 6.2 (p. 37): "[On]^{<ω} is well-ordered by <*."

> 6.3 Definition. Let M be acceptable. The <*-least p ∈ P_M^n is called the
> n-th standard parameter of M and is denoted by p_n(M). We shall write M^n
> for M^{n,p_n(M)}; M^n is called the nth standard reduct of M.

> 6.6 Definition. Let M be acceptable. Suppose that for all n < ω, p_n(M) =
> p_{n+1}(M) ↾ n. Then we set p(M) = ⋃_{n<ω} p_n(M). p(M) is called the
> standard parameter of M.
>
> We shall often confuse p(M) with ran(p(M)).

Corollaries 6.5 and 6.7 (p. 37): "Let n > 0. Let M be n-sound. Then
p_{n−1}(M) = p_n(M) ↾ (n − 1)." and "Let M be sound. Then p(M) exists, i.e.,
for all n < ω, p_n(M) = p_{n+1}(M) ↾ n."

Terminology note: SZ never use the term "master code" anywhere in the
chapter (zero occurrences of "master" in the extracted text). The objects the
digest's OPEN item 5 calls "master codes" are SZ's "standard codes" A_M^p and
A_M^{n,p}; the digest's "A^n" shorthand corresponds, in SZ's notation, to
A_M^{n,p_n(M)} on the n-th standard reduct M^n (available when p_n(M) ∈
R_M^n; see Lemma 6.8 below).

## 3. The reduction theorems (the load-bearing target, digest OPEN item 5)

### 3.1 The chapter's own statement of the reduction program

After the Σ1-Skolem-function theorem, SZ state the reduction program in plain
words (SZ p. 14, end of the proof of Theorem 1.15), verbatim:

> If we were to define a Σ2 Skolem function for M in the same manner then we
> would end up with a Σ3 definition. Jensen solved this problem by showing
> that under favourable circumstances Σn over M can be viewed as Σ1 over a
> "reduct" of M. Reducts will be introduced in the fifth section of this
> chapter.

Note the qualifier: "under favourable circumstances". The chapter then gives
the circumstances precisely (very good parameters, and soundness for the
standard-parameter version; sections 3.2-3.4 below).

### 3.2 The master-code-style reduction as SZ state it

The exact reduction statement is SZ Lemma 5.6 (p. 34), verbatim:

> 5.6 Lemma. Let n < ω. Let M be acceptable and p ∈ R_M^n. Let A ⊆ M^{n,p}
> be Σ_{n+1}^M. Then A is Σ_1^{M^{n,p}}.

So: every Σ_{n+1}-over-M subset of the n-th reduct is Σ1 over the n-th
reduct, provided the parameter p is a very good parameter (p ∈ R_M^n). In
the digest's shorthand: Σ_{n+1} over M is captured by Σ1 over the n-th
reduct (master-code) structure M^{n,p}. Note the indexing: SZ's "n-th
reduct" carries the reduction from Σ_{n+1} down to Σ1, i.e. "Σ_n over J_α is
Σ1 over the (n−1)-th standard code" in the digest's numbering.

The companion level-by-level equality, SZ Lemma 5.5 (p. 34), verbatim:

> 5.5 Lemma. Let 0 < n < ω. Let M be acceptable, and let p ∈ R_M^n. Then
> Σ_ω^M ∩ P(M^{n,p}) = Σ_ω^{M^{n,p}}.

The hull machinery behind 5.5/5.6, SZ Lemmata 5.4 and 5.7 (p. 34): the
function h_M^{n+1} is the iterated composition of the Σ1 Skolem functions of
the ith reducts (SZ p. 33-34), and

> 5.4 Lemma. Let n < ω, and let M be acceptable. Then h_M^{n+1} is in Σ_ω^M,
> and
> M = h_M^{n+1}"(ρ_{n+1}(M) ∪ {p}),
> whenever p ∈ R_M^{n+1}.

> 5.7 Definition. M is n-sound iff R_M^n = P_M^n. M is sound iff M is n-sound
> for all n < ω.

followed by (SZ p. 34): "We shall prove later (cf. Lemma 9.2) that every J_α
is sound. In fact, a key requirement on initial segments of a core model is
that they be sound."

The soundness gate for the standard-parameter version, SZ Lemma 6.8 (p. 37),
verbatim:

> 6.8 Lemma. M is sound iff p_n(M) ∈ R_M^n for all n ∈ ω.

and SZ Lemma 9.2 (p. 52), verbatim: "For each limit ordinal α, J_α is
sound." So for L (and its levels), the reduction of section 3.2 holds with
the standard codes A_M^{n,p_n(M)} on the standard reducts; for arbitrary
acceptable structures it is stated with very good parameters instead.

### 3.3 The embedding-extension lemmata (downward and upward)

First projectum version: the downward extension of embeddings lemma is the
conjunction of Lemmata 3.1-3.3 (SZ p. 21, framing quote; statements on pp.
21, 23, 24), verbatim:

> Given a Σ0 preserving map between the reducts of two acceptable structures,
> the question naturally arises whether the map can be extended to a map
> between the original structures. It turns out that this is possible. The
> conjunction of the following three lemmas is called the downward extension
> of embeddings lemma.

> 3.1 Lemma. Let π : M̄^{p̄} →_{Σ0} M^p, where p̄ ∈ R_{M̄}. Then there is a
> unique π̃ : M̄ → M such that π̃ ⊇ π and π̃(p̄) = p. Moreover, π̃ : M̄
> →_{Σ1} M.

> 3.2 Lemma. Let M̄, M, p̄, p, π, π̃ be as above. Suppose moreover that p ∈
> R_M. Let π : M̄^{p̄} →_{Σ_n} M^p. Then
> π̃ : M̄ →_{Σ_{n+1}} M.

> 3.3 Lemma. Let π : N →_{Σ0} M^p, where N is a J-structure and p ∈ R_M.
> Then there are unique M̄, p̄ such that p̄ ∈ R_{M̄} and N = M̄^{p̄}.

Upward version: SZ define strong embeddings (SZ Definition 4.1, p. 26),
verbatim:

> 4.1 Definition. π : M̄ → M is a strong embedding iff
> a) π : M̄ →_{Σ1} M
> b) For any R̄, R such that R̄ is rudimentary over M̄ and R is rudimentary
> over M by the same definition the following holds:
> If R̄ is well-founded, then so is R.

and state the upward extension of embeddings lemma (SZ p. 26), verbatim:

> The upward extension of embeddings lemma is the conjunction of the
> following lemma together with Lemmata 3.1 and 3.2.
>
> 4.2 Lemma. Let π : M̄^{p̄} → N be a strong embedding, where N is acceptable
> and p̄ ∈ R_{M̄}. Then there are unique M, p such that N = M^p and p ∈ R_M.
> Moreover, π̃ is strong, where π̃ ⊇ π, π̃ : M̄ →_{Σ1} M and π̃(p̄) = p.

The proof (SZ pp. 26-32) encodes M̄ and its Σ1-satisfaction relation in a
rudimentary fashion over M̄^{p̄}, transfers by preservation, and takes the
transitive collapse; see section 6 for the exact dependencies invoked.

Iterated (n-th reduct) version, SZ Lemmata 5.8-5.11 (p. 35), verbatim:

> 5.8 Lemma. Let M̄, M be acceptable and π : M̄^{n,p̄} →_{Σ0} M^{n,p}, where
> p̄ ∈ R_{M̄}^n. Then there is a unique map π̃ ⊇ π such that dom(π̃) = M̄,
> π̃(p̄) = p and, setting π̃_i = π̃ ↾ H_{M̄}^i,
> π̃_i : M̄^{i,p̄↾i} →_{Σ0} M^{i,p↾i} for i ≤ n.
> The map π̃_i is in fact Σ1-preserving for i ∈ n.

> 5.9 Lemma. Suppose that M̄, M, p̄, p, π, π̃, π̃_i, i ≤ n, are as above and
> p ∈ R_M^n. Let π : M̄^{n,p̄} →_{Σ_ℓ} M^{n,p} where ℓ ∈ ω. Then
> π̃_i : M̄^{i,p̄↾i} →_{Σ_{ℓ+n−i}} M^{i,p↾i} for i ≤ n.
> Hence, π̃_0 : M̄ →_{Σ_{ℓ+n}} M.

> 5.10 Lemma. Let π : N →_{Σ0} M^{n,p}, where M is as above. Then there are
> unique M̄, p̄ such that p̄ ∈ R_{M̄}^n and N = M̄^{n,p̄}.
> The general upward extension of embeddings lemma is the conjunction of the
> following lemma together with Lemmata 5.8 and 5.9.
> 5.11 Lemma. Let π : M̄^{n,p̄} → N be strong, where M̄ is an acceptable
> J-structure and p̄ ∈ R_{M̄}^n. Then there are unique M, p such that M is
> acceptable, p ∈ R_M^n and M^{n,p} = N. Moreover, if π̃ is as in Lemma 5.8,
> then π̃ is strong.
> If π and π̃ are as in Lemma 5.8 then π̃ is often called the n-completion of
> π.

Lemma 5.9 is the iterated form of the reduction-as-embedding-extension: a Σ_ℓ
map between the n-th reducts extends to a Σ_{ℓ+n} map between the full
structures. Combined with Lemma 5.6, this is exactly the sense in which
"Σ_n over M is Σ1 over the n-th reduct" is a theorem of this chapter.

### 3.4 The rΣ_{n+1} formulation and its role

SZ then package the preservation notion (SZ pp. 35-36), verbatim:

> It turns out that there is a canonical class of formulae, the so called
> Σ_ℓ^{(n)}-formulae, such that the above embeddings are exactly those which
> are elementary with respect to this class. This idea leads towards Jensen's
> elegant Σ∗ theory which is dealt with in [15, Sections 1.6 ff.].
> Following [8, §2], though, we shall call Σ_1^{(n)} elementary maps rΣ_{n+1}
> elementary. Here is our official definition, which presupposes that the
> structures involved possess very good parameters; it will play a rôle in
> the last two sections.
> 5.12 Definition. Let M, N be acceptable, let π : M → N, and let n < ω.
> Then π is called rΣ_{n+1} elementary provided that there is p ∈ R_M^n with
> π(p) ∈ R_N^n, and for all i ≤ n,
> π ↾ H_{ρ_i(M)}^i : M^{i,p↾i} →_{Σ1} N^{i,π(p)↾i}. (I.22)
> The map π is called weakly rΣ_{n+1} elementary provided that there is p ∈
> R_M^n with π(p) ∈ R_N^n, and for all i < n, (I.22) holds, and
> π ↾ H_{ρ_n(M)}^n : M^{n,p} →_{Σ0} N^{n,π(p)}.
> If π : M → N is (weakly) rΣ_{n+1} elementary then typically both M and N
> will be n-sound; however, neither M nor N has to be (n + 1)-sound. It is
> possible to generalize this definition so as to not assume that very good
> parameters exist (cf. [8, §2]).

and (SZ p. 36): "Lemma 5.8 therefore says that the map π can be extended to
its n-completion π̃ which is weakly rΣ_{n+1} elementary, and Lemma 5.9 says
that if π is Σ1 elementary to begin with then the n-completion π̃ will end up
being rΣ_{n+1} elementary."

SZ Lemma 5.13 (p. 36), verbatim: "Let n < ω, and let M, N be acceptable. Let
π : M → N be rΣ_{n+1} elementary. Then for all appropriate x, π(h_M^{n+1}(x))
= h_N^{n+1}(π(x))."

### 3.5 Verdict for the digest's OPEN item 5

SZ DO state the reduction, in the form of Lemma 5.6 (Σ_{n+1} over M is Σ1
over the n-th reduct, for p ∈ R_M^n) plus Lemma 5.9 (the embedding-extension
Σ-shift) and the chapter-level statement on p. 14. SZ do NOT state a
one-line theorem literally of the form "Σ_n over J_α is Σ1 over (J_{ρ_n},
A_n)"; that phrasing is the digest's shorthand. The exact form SZ give needs
(i) an acceptable J-structure, (ii) a very good parameter p (Lemma 5.6), and
(iii) soundness when the parameter is required to be the standard parameter
p_n(M) (Lemmata 6.8 and 9.2). Nothing in the chapter supports a parameter-free
or soundness-free version.

## 4. "Simple" functions (digest OPEN item 4)

The stem "simple" occurs five times in the whole chapter: twice inside the
technical definition in the proof of Lemma 1.4 (SZ p. 8) and three times in
prose (SZ pp. 27, 36, 52):

1. The technical definition, inside the proof of Lemma 1.4 (SZ p. 8),
   verbatim (already collected in rudimentary-functions.md section 4.1):

> "⊆": Call a function f : V^k → V, where k < ω, simple iff the following
> holds true: if ϕ(v_0, v_1, ..., v_m) is Σ0 in the language L_Ȧ with ˙∈ and
> Ȧ, then ϕ(f(v_1', ..., v_k'), v_1, ..., v_m) is equivalent over transitive
> rud_A closed structures to a Σ0 formula in the same language. It is not
> hard to verify inductively that every rud_A function is simple. (Here we
> use the hypothesis that A ∩ V^{rk(U)+ω} ⊆ U which ensures that in this
> situation quantifying over A is tantamount to quantifying over A ∩ U.)

2. Prose in the upward-extension proof (SZ p. 27): "The idea of the
   construction is simple: ..." (about the encoding idea, not a defined
   notion).
3. Prose at the start of section 6 (SZ p. 36): "Finite sets of ordinals are
   well-ordered in a simple canonical way."
4. Prose at the start of section 9 (SZ p. 52): "we shall illustrate how to
   use the above machinery in the simplest case, in the constructible
   universe L."

Verdict: the term "simple" does NOT reappear beyond Lemma 1.4's proof, and
nowhere in the chapter is a Σ_n-preservation or Σ*-theoretic role claimed for
simple functions. The digest's OPEN item 4 is settled for the SZ chapter:
NOT IN CHAPTER. (The role, if any, would live in Zeman's book [15, Sections
1.6 ff.] or Welch's [14], both cite-only in this collection; the chapter
points at [15]/[14] only for Σ* itself, see section 5.)

## 5. The Sigma-star machinery (digest OPEN item 4, second half)

SZ explicitly exclude Jensen's Σ* theory from the chapter (SZ p. 5,
introduction), verbatim:

> The present chapter will discuss the "pure" part of fine structure theory,
> the one which is not linked to any particular kind of constructible model
> one might have in mind. We shall discuss Jensen's classical version of this
> theory. We shall not, however, deal with Jensen's Σ∗ theory (which may be
> found in [15, Sections 1.6-1.8] or in [14]), and we shall also ignore other
> variants of the fine structure theory which have been created.

The only other substantive mention (SZ p. 36, quoted in section 3.4) presents
the Σ_ℓ^{(n)}-formulae as leading towards Σ*: "This idea leads towards
Jensen's elegant Σ∗ theory which is dealt with in [15, Sections 1.6 ff.]."
The bibliography entry [14] (SZ p. 57): "Philip Welch. Σ∗ fine structure. In
this Handbook." Here [15] = Zeman, "Inner models and large cardinals", de
Gruyter, 2002 (SZ p. 57), and [14] = Welch's Handbook chapter.

What this chapter uses instead of Σ*: the rΣ_{n+1} elementary maps
(Definition 5.12, p. 36, following Mitchell-Steel [8, §2]) and the derived
"n-embeddings" (Definition 7.13, p. 42). In SZ's own words (p. 36), the
Σ_ℓ^{(n)} class is the canonical class of formulae for the level-by-level
embeddings, but the chapter does not develop the class itself; it "officially"
defines and uses rΣ_{n+1} elementary maps instead.

## 6. What fine structure needs from the base apparatus (dependency list)

The fine-structure sections (2-8) are stated uniformly for acceptable
J-structures, and their proofs lean on the section-1 machinery as follows.

1. Acceptability of M is a standing hypothesis: every definition in the
   fine-structure sections opens "Let M be acceptable" (Definitions 2.1, 2.5,
   2.6, 2.8 pp. 19-21; 5.1, 5.2 p. 32; 6.3 p. 37; 7.1, 7.5 pp. 39-41; 8.1,
   8.6, 8.9, 8.11 pp. 42-50). The section-2 framing adds (SZ p. 19): "We
   stress that we are working with arbitrary J-structures and that these
   structures have, in general, very few closure properties."
2. The reduct is amenable automatically: Corollary 2.4(a) (p. 19), "If B ⊆
   J_ρ^A is Σ_1^M, then ⟨J_ρ^A, B⟩ is amenable", which rests on Lemma 1.23
   (acceptability) and Lemma 1.17 (Σ1 surjection ρ → J_ρ^A, p. 15).
3. rud_A-closedness plus amenability of M, explicitly used inside the
   ultrapower construction: "Notice that the relevant sets are members of M,
   as M is rud_A-closed and amenable" (SZ p. 44, proof of Theorem 8.4) and
   "The point is that f_0 ∈ M, because M is rud_A-closed and amenable"
   (SZ p. 45, the Loś theorem step).
4. Amenability of N as the ambient condition for bounded Σ1-definability in
   the upward-extension proof: "Since N is amenable, every bounded Σ_1^M
   subset of ρ is an element of N" (SZ p. 31, proof of Lemma 4.2).
5. The rudimentary encodability of a structure and its satisfaction relation
   over its own reduct: "using the fact that p̄ ∈ R_{M̄}, we encode the whole
   structure M̄ and its satisfaction relation in a rudimentary fashion over
   M̄^{p̄}" (SZ p. 27, proof of Lemma 4.2), and the conclusion that the
   Σ1-satisfaction relation T̄ of the encoded structure is "Σ_1^{M̄} in p̄ and
   therefore rudimentary over M̄^{p̄}" (SZ p. 28).
6. The Lemma 1.4 hypothesis A ∩ V^{rk(U)+ω} ⊆ U (p. 8), with SZ's own remark
   (p. 8): "The hypothesis that A ∩ V^{rk(U)+ω} ⊆ U in Lemma 1.4 is needed
   to avoid pathologies; it is always met in the construction of fine
   structural inner models."
7. The Σ1-satisfaction and Skolem-function theorems (1.14-1.15, p. 13), the
   uniform Σ1-ness of the S-hierarchy and well-orders (1.10-1.11, pp. 11-12),
   and Lemma 1.17 (p. 15): all are invoked inside the proofs of 2.3, 2.9,
   3.1-3.3, 4.2, 5.4-5.6.
8. Very good parameters are presupposed by the official Definition 5.12
   (p. 36): "which presupposes that the structures involved possess very good
   parameters", with the alternative noted as "(cf. [8, §2])". The remark on
   p. 21 records that P_M and R_M are often defined differently in the
   literature.
9. Q-formulae and Q-properties are a section-1 tool only: they are used for
   acceptability (Definition 1.18, p. 15; Lemma 1.21, p. 16) and its
   preservation (Corollary 1.22, p. 17). The fine-structure sections 2-9 do
   not mention Q again.
10. For the ultrapower theorems: soundness and solidity of the source model
    (8.6-8.7, pp. 48-49: "Suppose that M is n-sound", "Suppose that M is
    n-sound and (n + 1)-solid"), and for Theorem 8.10 (p. 49) additionally a
    short extender close to M (Definition 8.9, p. 49).

## 7. The remaining fine-structure sections, in brief (with pages)

Solidity witnesses (section 7, pp. 39-42): Definition 7.1 (p. 39) defines
(W, r) a witness for ν ∈ p w.r.t. M, p; Lemma 7.2 (p. 39) "Let M be an
acceptable structure, and let p ∈ P_M. Suppose that for each ν ∈ p there is a
witness W for ν ∈ p w.r.t. M, p such that W ∈ M. Then p = p_1(M).";
Definition 7.3 (p. 40) defines the standard witness W_M^{ν,p} as the
transitive collapse of h_M(ν ∪ (p \ (ν + 1))); Definition 7.5 (p. 41): M is
1-solid iff W_M^{ν,p_1(M)} ∈ M for every ν ∈ p_1(M); Definition 7.10 (p. 41)
extends to n-solid; Definition 7.13 (p. 42) defines n-embeddings: both models
n-sound, π rΣ_{n+1} elementary, π(p_k(M)) = p_k(N) for k ≤ n, and
π(ρ_k(M)) = ρ_k(N) for k < n with ρ_n(N) = sup(π"ρ_n(M)). The nth core C_n(M)
is introduced on p. 42 as the transitive collapse of h_M^n"(ρ_n(M) ∪
{p_n(M)}), "called the nth core of M", with "The natural map from C_{n+1}(M)
to C_n(M) will be an n-embedding under favourable circumstances."

Fine ultrapowers (section 8, pp. 42-52): Definition 8.1 (p. 42) defines
(κ, ν)-extenders over acceptable M; Theorem 8.4 (p. 43) constructs the Σ0
ultrapower with the Loś theorem (proof pp. 44-47); Definition 8.5 (p. 47)
names it Ult_0(M; E); Definition 8.6 (p. 48): Ult_n(M; E), the rΣ_{n+1}
ultrapower, requires ρ_n(M) > σ(E), M n-sound, and uses "the proof of
Lemmata 4.2 and 5.11" (upward extension), with the comment that the term-model
construction does not require π to be strong nor N̄ well-founded; Theorem 8.7
(p. 48) shows the rΣ_{n+1} ultrapower map is an n-embedding (assuming
(n + 1)-solidity and transitivity); Theorem 8.10 (p. 49) is "the key tool for
proving the preservation of the standard parameter in iterations of mice":
for a short extender E close to M with ρ_{n+1}(M) ≤ κ < ρ_n(M), M n-sound,
Ult_n(M; E) transitive, one gets P(κ) ∩ M = P(κ) ∩ Ult_n(M; E) and
ρ_{n+1}(M) = ρ_{n+1}(Ult_n(M; E)); Corollary 8.13 (p. 51): an ℵ0-complete
extender gives well-founded Ult_0(M; E), and if ρ_n(M) ≥ σ(E) then Ult_n(M; E)
is well-founded.

Applications to L (section 9, pp. 52-56): Lemma 9.1 (p. 52) "For each limit
ordinal α, J_α is acceptable." and Lemma 9.2 (p. 52) "For each limit ordinal
α, J_α is sound.", proved simultaneously "in a zig-zag way in the sense that
we use soundness of J_α to prove the acceptability of J_{α+ω} and then,
knowing this, its soundness" (SZ p. 52). The proof of 9.1 uses ρ_ω(J_β) =
τ (equation (I.31), p. 52) and Lemma 5.6 (p. 53: "Lemma 5.6 then yields that
a is Σ_1^{J_β^{n−1}}, since, by the induction hypothesis, J_β is sound.").
The proof of 9.2 (p. 53) uses Lemma 6.8 and the downward extension lemma,
with the map of equation (I.33). Then Theorem 9.3 (p. 53) is the Covering
Lemma for L: "Suppose that 0# does not exist. Let X be a set of ordinals.
Then there is Y ∈ L with Y ⊇ X and Card(Y) ≤ Card(X) · ℵ1." (cited to [2]
and [5]); Corollary 9.4 (p. 53) and Theorem 9.5 (p. 54, "Suppose that V = L.
Let κ ≥ ℵ1 be a cardinal. Then ◇κ holds.", proof pp. 55-56) close the
chapter.

## 8. Degradation notes and open items

### DEGRADED

- Definition 5.1 (p. 32): pdftotext drops the "n,p" superscript on M in
  "min{ρ(M^{n,p}); p ∈ Γ_M^n}" and the sub/superscript structure of A_M^{n+1,p}
  and M^{n+1,p}; restored per context and confirmed by Lemma 5.3(b)-(c)
  (p. 33). The ∏ over i ∈ n+1 is restored from the layout artifact.
- Definition 5.1 remark (p. 32): the extraction reads "≤ ⋯ ≤ Sρ1 (M)" with a
  stray glyph "S"; restored to "ρ_n(M) ≤ ⋯ ≤ ρ_1(M)", semantically forced by
  the following identification of p with ran(p).
- Definition of h_M^{n+1} (p. 34): the domain "ω^{<ω} × |M^{n+1,p}|^{<ω}" loses
  both "<ω" exponents in extraction; restored from the recursion (finite
  sequences of indices/arguments).
- Lemma 3.1 (p. 21): the Σ0/Σ1 subscripts under the arrows are dumped at the
  end of the line in extraction; restored to the only reading consistent with
  the section's framing and with Lemmata 3.2 and 5.8.
- SZ p. 14 and p. 36: "Σn over M", "Σ1 over a 'reduct'", "Σ_ℓ^{(n)}",
  "rΣ_{n+1}" superscript/subscript positions restored from layout artifacts.
- SZ p. 8 quote in section 4: "L_Ȧ", "˙∈", "Ȧ" (language with dotted
  predicates) restored from the extraction's "LȦ" artifacts; meaning
  unambiguous.

### OPEN (unresolvable from this chapter alone)

- The content of Jensen's Σ* theory itself, and any Σ*-theoretic role of
  "simple" functions: NOT IN CHAPTER; SZ point to [15, Sections 1.6 ff.] and
  [14] (pp. 5, 36), both cite-only in this collection. Fetching Zeman's book
  sections or Welch's chapter would settle it.
- Whether Zeman's book [15] states the master-code reduction in the digest's
  literal "(J_{ρ_n}, A_n)" form: NOT DETERMINABLE from this chapter; the SZ
  form is Lemma 5.6 (section 3.2 above).
