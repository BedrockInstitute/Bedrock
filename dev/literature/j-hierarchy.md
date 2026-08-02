# The J-hierarchy, S vs J stratification, condensation, well-order, acceptability

Developer notes for the rud-route formalization. Primary source: SZ =
Schindler & Zeman, "Fine structure", Handbook of Set Theory (author preprint;
PDF internal pages 5-58, cited below as SZ p. N). Secondary fetched sources:
MB = Mathias & Bowler (preprint pages), WS = Mathias, Weak systems (preprint
pages), Fr = Mathias, Freiburg slides. Full citations in BIBLIOGRAPHY.md.

Extraction note: pdftotext degrades some math glyphs (union appears as S,
member-of as 2, Delta/Sigma subscripts as 0/1); quotes restore the intended
symbols where unambiguous.

## 1. S vs J stratification (Q2)

SZ Definition 1.6 (p. 9), verbatim (symbols restored):

> Let A be a set or a proper class.
>
> J_0^A     = ∅
> J_{α+ω}^A = rud_A(J_α^A ∪ {J_α^A})
> J_{ωλ}^A  = union_{α<λ} J_{ωα}^A  for limit λ
> L[A]      = union_{α∈On} J_{ωα}^A
>
> Every J_α^A is rud_A closed and transitive. We shall also denote by J_α^A the
> structure <J_α^A, ∈↾J_α^A, A ∩ J_α^A>.

The indexing convention is deliberate and stated (SZ p. 9, before Def. 1.6):

> For later purposes it is convenient to index this hierarchy by limit ordinals.

with footnote 4: "This is again in contrast with [3]." Here [3] = Jensen 1972
(SZ bibliography, p. 57). So: SZ index J by limit ordinals; Jensen's original
paper indexed differently; the fetched text does not spell out Jensen's indexing
convention, so the contrast is reported as stated in footnote 4 without further
detail.

The auxiliary S-hierarchy (SZ p. 9), verbatim:

> It is often necessary to work with the auxiliary hierarchy S^A_α of [3, p.
> 244] which is defined as follows:
>
> S_0^A     = ∅
> S_{α+1}^A = S^A(S_α^A)
> S_λ^A     = union_{ξ<λ} S_ξ^A  for limit λ
>
> where S^A is an operator which, applied to a set U, adds images of members of
> U ∪ {U} under rud_A functions from a certain carefully chosen fixed finite
> list.

S^A(U) = union_{i=0}^{15} F_i"(U ∪ {U})^2 with the F0..F15 list (SZ p. 10);
see rudimentary-functions.md section 1.2. The bridge between the hierarchies
(SZ p. 10), verbatim:

> Every S_α^A is transitive, and moreover
>
> J_α^A = S_α^A            (I.1)
>
> for all limit ordinals α. It is easy to see that there is only a finite jump
> in rank from S_α^A to S_{α+1}^A. A straightforward induction shows that J_α^A
> ∩ On = α for all limit ordinals α.

Footnote 5 (SZ p. 10): the F0..F15 list "in fact contains more functions than
the list from [3, Lemma 1.8]; this enlargement yields the transitivity of each
S_α^A."

SZ 1.9 Definition (p. 11): "A J-structure is an amenable structure of the form
<J_α^A, B> for a limit ordinal α and predicates A, B."

SZ 1.10 Lemma (p. 11): for β < α, <S_γ^A ; γ < β> ∈ J_α^A, and <S_γ^A ; γ <
α> is uniformly Σ_1^{J_α^A} ("x = S_γ^A" is Σ1 over J_α^A as witnessed by a
formula which does not depend on α).

The omega-times-alpha issue appears in two fetched places:

1. SZ p. 17 (proof of Lemma 1.21): "If the height of M is ωα for some limit α,
   then acceptability is equivalent to the statement Qξ S_ξ^A |= ψ."
2. MB 0.3 EXAMPLE (p. 2) and Fr slide 14: Jν = T_{ων}, and "ν -> ων is not rud
   rec" (Fr slide 14). MB p. 31: "it is clear by induction that Jν = P^∅_{ω·ν}
   for any ν" (in the canonical-progress notation of MB section 6).

Contemporary preferred stratification: SZ's J-hierarchy indexed by limit
ordinals (Def. 1.6 + footnote 4), with the S-hierarchy as the step-by-step
auxiliary (SZ p. 9); MB works with Jν = T_{ων} and the strict continuous
progresses P^c_ν (MB sections 6-7).

## 2. Condensation (Q2)

SZ Theorem 1.16 (p. 14), verbatim:

> Let M = <J_α^A, B> be a J-structure, and let π : M̄ ->_Σ1 M where M̄ is
> transitive. Then M̄ is a J-structure, i.e., there are ᾱ ≤ α, Ā, and B̄ such
> that M̄ = <J_{ᾱ}^{Ā}, B̄>.

So condensation lives at the Sigma_1 level in SZ. Footnote 6 (p. 14) explains
the arrow notation: "For n < ω, X ≺_Σn M means that Σn formulae with parameters
taken from X are absolute between X and M. To have π : M̄ ->_Σn M means that
ran(π) ≺_Σn M."

Proof shape (SZ p. 14): set ᾱ = On ∩ M̄ ≤ α, Ā = π^{-1}"A, B̄ = π^{-1}"B; use
Lemma 1.10 to get S_β^{Ā} ∈ M̄ for β < ᾱ, so J_{ᾱ}^{Ā} ⊆ M̄; conversely each
x ∈ M̄ has π(x) ∈ S_β^A for some β < α, hence x ∈ S_β^{Ā}.

Supporting machinery:

- SZ 1.14 Theorem (p. 13): the Σ1-satisfaction relation |=_Σ1^M is uniformly
  Σ_1^M.
- SZ 1.15 Theorem (p. 13): every J-structure M has a Σ_1^M-deﬁnable Σ1 Skolem
  function h^M. The proof picks the "first component" of a minimal witness,
  using N = S_β^A and R = <^A_β (Lemmata 1.10(2), 1.11(2)).
- SZ 1.17 Lemma (p. 15): there is a surjective f : [α]^<ω -> M which is Σ_1^M;
  if α is closed under the Gödel pairing function then there is a surjection
  g : α -> J_α^A which is Σ_1^M; for arbitrary α there is a surjection h : α ->
  J_α^A which is Σ_1^M (the last by [3, Lemma 2.10]).
- SZ 1.22 Corollary (p. 17): (a) if π : M̄ ->_Σ1 M and M is acceptable, then so
  is M̄; (b) if π : M̄ ->_Q M and M̄ is acceptable, then so is M, "in particular
  if π is a Σ0 preserving cofinal map."

## 3. The canonical well-order (Q4)

SZ p. 11 defines <^A_β on S_β^A recursively. Verbatim (symbols restored):

> We may recursively define a well-ordering <^A_β of S_β^A as follows. If β is a
> limit ordinal then we let <^A_β = union_{γ<β} <^A_γ. Now suppose that β = β̄ +
> 1. The order <^A_{β̄} induces a lexicographical order, call it <^A_{β̄,lex}, of
> 16 × S_{β̄}^A × S_{β̄}^A. We may then set
>
> x <^A_β y ⇐⇒   x, y ∈ S_{β̄}^A and x <^A_{β̄} y, or else
>                 x ∈ S_{β̄}^A and y ∉ S_{β̄}^A, or else
>                 x, y ∉ S_{β̄}^A and (i, u_x, v_x) <^A_{β̄,lex} (j, u_y, v_y)
>                   where (i, u_x, v_x) is <^A_{β̄,lex}-minimal with
>                   x = F_i(u_x, v_x) and (j, u_y, v_y) is <^A_{β̄,lex}-minimal
>                   with y = F_j(u_y, v_y).

The "producer/stage" picture is exactly the finite basis F_i with the
lexicographic triple (i, u, v) of the producer index and the arguments; older
stages S_{β̄}^A precede newer ones. This matches the raw sweep's "producer/stage
order" description: stage comparison first (x ∈ S_{β̄}^A vs not), then the
minimal producer triple within the new stage.

SZ 1.11 Lemma (p. 11), verbatim:

> (1) For all β < α, < <^A_γ ; γ < β> > ∈ J_α^A. In particular, <^A_β ∈ J_α^A
> for all β < α.
> (2) < <^A_γ ; γ < α> > is uniformly Σ_1^{J_α^A}. That is, "x = <^A_γ" is Σ1
> over J_α^A as witnessed by a formula which does not depend on α.

SZ 1.17 (p. 15) uses the well-order for the enumeration: "let Φ : otp(<^A_α) ->
J_α^A denote the enumeration of J_α^A according to <^A_α", with "if α is closed
under the Gödel pairing function then otp(<^A_α) = α."

## 4. Acceptability (Q2)

SZ Definition 1.20 (p. 16), verbatim:

> A J-structure M = <J_α^A, B> is acceptable iff the following holds: Whenever ξ
> < α is a limit ordinal and P(τ) ∩ J_{ξ+ω}^A ⊄ J_ξ^A for some τ < ξ, there is
> a surjective map f : τ -> ξ in J_{ξ+ω}^A. (This means that Card(ξ) ≤ τ in
> J_{ξ+ω}^A.)

The remark after the definition (SZ p. 16): "As will follow from the definition,
acceptability can be considered as a strong version of GCH."

SZ 1.21 Lemma (p. 16): "Being an acceptable J-structure is a Q-property. More
precisely: There is a fixed Q-sentence Ψ such that for any M = <|M|, A, B> which
is transitive and closed under pairing, M is an acceptable J-structure iff M |=
Ψ." The proof (pp. 16-17) rephrases acceptability as (I.2), using S_ξ^A instead
of J_ξ^A:

> ∀ limit ordinals ξ ∃ n ∈ ω ∀ m ≥ n ∀ τ < ξ
> [P(τ) ∩ S_{ξ+m}^A ⊄ S_ξ^A =⇒ ∃ f ∈ S_{ξ+m}^A, f : τ -> ξ onto].

and builds the Q-sentence (I.3) with the "last level" case handled by the
auxiliary sentence φ.

SZ 1.22 Corollary (p. 17): acceptability is preserved downward by Σ1
embeddings and upward by Q-embeddings (quoted in section 2 above).

SZ 1.23-1.27 (pp. 17-18) derive the consequences: for acceptable M = J_α^A and
ρ ∈ M an infinite cardinal in M, subsets of elements of J_ρ^A that lie in M are
in J_ρ^A (1.23); J_ρ^A |= ZFC- for ρ an infinite successor cardinal (1.25); J_ρ^A
|= ZC for ρ > ω a limit cardinal (1.26); |J_ρ^A| = H_ρ^M (1.27).

Applications to L (SZ section 9, p. 52), verbatim:

> We shall first prove two important lemmata. Recall that we index the
> J-hierarchy with limit ordinals.
> 9.1 Lemma. For each limit ordinal α, Jα is acceptable.
> 9.2 Lemma. For each limit ordinal α, Jα is sound.

proved simultaneously "by induction on α in a zig-zag way in the sense that we
use soundness of Jα to prove the acceptability of J_{α+ω} and then, knowing
this, its soundness" (SZ p. 52). Section 9 then proves the Covering Lemma for L
(9.3, cited to [2] = Devlin-Jensen, "Marginalia to a theorem of Silver") and
♦κ in L (9.5). SZ do not prove GCH in L in this chapter; the GCH connection in
the fetched text is only the "strong version of GCH" remark at Definition 1.20.

## 5. Source-consumption map

- SZ: all sections (primary).
- MB: section 1 (omega-times-alpha, Jν = T_{ων}).
- WS: cited via MB; the J-hierarchy itself is not re-developed in WS beyond
  the rud machinery (see rudimentary-functions.md).
- Fr: slide 14 (Jν = T_{ων}; ν -> ων not rud rec); slide 28 (Jω provident, next
  is J_{ω^2}).
