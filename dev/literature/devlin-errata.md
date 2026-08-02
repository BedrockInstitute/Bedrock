# Devlin errata: documented error classes (do-not-repeat checklist)

Developer notes for the rud-route formalization. The two named accounts in the
raw sweep:

1. Stanley's JSL review of Devlin's "Constructibility": full text is paywalled
   (Project Euclid and JSTOR both show metadata only; see BIBLIOGRAPHY.md).
   Direct content from the review itself = NOT fetched. Everything below that
   is attributed to Stanley is quoted from Mathias's account (WS section 10)
   or from the Welch draft, not from the review.
2. Mathias's account: WS = Mathias, "Weak systems of Gandy, Jensen and Devlin",
   section 10 "MENDING THE FLAWS IN DEVLIN'S BOOK" (preprint pp. 56-66),
   fetched in full.

Supporting fetched sources: MB = Mathias & Bowler (preprint), W = Welch draft
"Syntax without arithmetic or concatenation" (2012, secondary, symbol-degraded
text). Page numbers below are preprint internal pages.

## 1. Status of the Stanley review itself

Metadata fetched from Project Euclid (wayback snapshot of
euclid.jsl/1183742450) and JSTOR (wayback snapshot of stable/2274371), agreeing:

- Lee J. Stanley, "Review: Keith J. Devlin, Constructibility", Journal of
  Symbolic Logic, Vol. 52, Issue 3 (Sep. 1987), pp. 864-867.
- JSTOR DOI 10.2307/2274371; Project Euclid permanent link
  https://projecteuclid.org/euclid.jsl/1183742450.

Discrepancy: MB's own bibliography (p. 40) cites the review as "Journal of
Symbolic Logic 53 (1987) 864-8"; WS's bibliography (p. 76) cites it as "Journal
of Symbolic Logic 53 (1982?) 864-8". The fetched journal metadata (52, 1987,
864-867) is authoritative for the citation; both Mathias papers carry the
volume slip. Report this in the checklist: do not copy the 53 from either
Mathias bibliography.

What the fetched text says the review contains:

- WS section 10 opening (p. 56): "We turn now to a discussion of the flaws in
  Devlin's book Constructibility to which attention was drawn in Stanley's
  review mentioned in a previous section. The problems are chiefly confined to
  section 9 of Chapter I and section 1 of Chapter VI."
- WS 10.24 (p. 66): "the second is GJI, which apart from the restraint to Π1
  foundation, is the system RUD discussed in Stanley's review".
- W p. 1: "Unfortunately as is now well known (see the review in particular of
  Stanley [6]) BS is not up to the task, although assuming that ω is a set, it
  cannot prove the existence of sets such as [ω]^3 the set of all 3 element
  subsets of ω"; and W p. 1: "Mathias suggests three systems to remedy the
  defects in BS, one of which - as also suggested by Stanley - is the theory of
  BS augmented by the rudimentary functions, or in essence GJ augmented by an
  axiom of infinity."

UNVERIFIED marker: any claim about the specific wording of Stanley's review is
UNVERIFIED, because the review itself is paywalled and not fetched; the content
above comes from Mathias's and Welch's accounts of it.

## 2. Mathias's systematic inventory (WS section 10, pp. 56-66)

### 2.1 General problems (not confined to Devlin)

- Levels-of-language ambiguity. WS p. 56-57: "There is an ambiguity over the
  meaning of Δ0 (which Devlin calls Σ0)." Devlin (p. 230) gives two definitions
  of a Σ0 function: a class term {(y, x~) | Φ(y, x~)} with Φ a Σ0 formula of
  LST, versus a function f with a Σ0 φ of L such that for any transitive M
  containing the arguments, f(x~) = y ⇐⇒ |=_M φ(ẏ, x~). WS 10.1 REMARK: the
  second definition collapses if TCo is false, "Thus Devlin's remark that the
  two definitions are 'equivalent' is dangerous."
- Notation: Devlin conflates (X × X) × X with X × (X × X) (WS 10.0, p. 56);
  the variants matter in weak systems (models of BS containing one but not the
  other of the two iterated products exist, WS 10.0).

### 2.2 Errors in Chapter I, section 9 (WS pp. 57-63)

Error classes in checklist form (each with WS item and verdict):

- Finseq definition (10.2): as printed, members of Finseq are functions with
  domain "a non-empty bounded subset of ω (possibly not a proper initial
  segment)". Fix: domain a non-empty bounded initial segment. Still Δ0.
- Lemma 9.1, 9.2: correct ("Lemmata 9.1 and 9.2 are correct", p. 57).
- F∧ uses addition (p. 57): the clause "Dom(θ) = Dom(φ) + Dom(ψ) + 3" occurs,
  so concatenation needs addition of natural numbers.
- Lemma 9.3 "F∧ is Δ0": FALSE. WS p. 57-58: "Solovay has remarked that that
  can be seen by Ehrenfeucht-Fraïssé games"; and via Gandy, every Δ0 subset of
  ω is finite or cofinite, the graph of addition is not Δ0, hence neither is
  the graph of concatenation. Corrected: F∧ is Δ^BS_1 (WS 10.3 PROPOSITION,
  p. 58, via an attempt at addition).
- Build (p. 59): the definition admits "junk" (sequences with extra atomic
  formulas) unless a minimality condition excludes it; "some minimality
  condition is needed, to the effect that every formula listed is actually a
  subformula of the formula being built."
- Lemma 9.4 "Build(φ, ψ) is Δ0": proof invalid (uses 9.3); statement suspect.
  Corrected: Build is Δ^BS_1 (WS 10.4 PROPOSITION, p. 59).
- Seq (p. 59): the formula Seq(u, a, n) is correctly stated to be Σ1, but
  Lemma 9.5 "Seq is Δ^BS_1" is FALSE per Solovay ("as may be seen using a
  forcing argument"). WS shows in Model 6 there is no u with Seq(u, ω, 4), and
  the claim "BS ⊢ (∀a)(∀n∈ω)(∃u)Seq(u, a, n)" (Devlin p. 37 lines 5-6) is not
  a theorem of BS, as shown by Model 9 (no u with Seq(u, {ω} × ω, 4)) and Model
  6 (10.5, p. 59-60).
- Bounding quantifiers (10.6, p. 60): the proposed bounding class for the
  quantifier f in the proof of 9.5 is (a) not provably a set (Model 5 omits the
  set BIN of finite binary sequences), and (b) the wrong type ("The values of f
  are not finite sequences but sets of finite sequences").
- Lemma 9.6 "Fml(x) is Δ^BS_1": the statement is true but the proof is
  seriously flawed: a typo in A(x) ("replace the third occurrence of 'n' by
  'm'"), and "the claim 'BS ⊢ ∀x∃y[y = A(x)]' is untrue; as is shown by Model
  9, for appropriate infinite x". Fix: A(x) exists for finite sequences
  (WS 10.10 LEMMA, provable in ReS), and use Build ∈ Δ^BS_1 twice (WS p. 61).
- Lemma 9.7: "The above arguments, appropriately modified, will prove Lemma
  9.7."
- Fr (10.11, p. 61): the definition of Fr involves a recursion on a finite
  tree; "Perhaps there is some general principle that GJ suffices for such but
  that BS is too weak." Lemma 9.8 "Fr is Δ^BS_1": true, but needs Metatheorem
  2.32, and uniqueness of the x for which Fr(φ, x) holds should be proved given
  the wide range of building sequences.
- Sub (p. 61): "the scope of this quantifier" is used but not defined; Lemma
  9.9 "Sub is Δ^BS_1" again needs the F∧-style recursion; "Fifth line from the
  bottom of page 39: for F∈ read F∃."
- Sat (p. 62): "there is a real problem on page 41 for which our cure will not
  work: w(u, φ) may not be a set, as is shown by Model 9" (k-sequences from an
  infinite set). Lemma 9.10 "the LST formula Sat(u, φ) is Δ^BS_1" is FALSE:
  "In Model 6, for no infinite set x does there exist a y with Seq(y, x, 4)...
  the given Σ1 formula for Sat(u, φ) will always be false; but then so is the
  Σ1 version of Sat(u, qφ); but one of them ought to be true!" No cure in BS.
- Lemma 9.12: follows from the amended 9.6 and 9.7 (p. 62).

### 2.3 Errors in Chapter II (WS pp. 62-63)

- Amenability (Devlin p. 45, section 10): Devlin defines amenable as transitive
  plus 5 conditions, including closure under "Δ̇0(M) separators" (Devlin writes
  "Σ0"); WS: "the length of φ is quantified in the language of discourse; it
  might well be that each φ is in M; but if M is non-standard it may think
  differently about what wffs are possible." WS suggests defining amenable as
  transitive + contains ω + closed under the finite set of generators of B.
- Uniformity claim (Devlin p. 65): the claim that Sat is uniformly Δ^M_1 for
  amenable M is false; WS gives a counterexample with Model M6,5 (pp. 62-63):
  "Let u be an infinite transitive set containing only finitely many sets of
  cardinality 5...", and 10.12 REMARK argues "no other pair of Π1 and Σ1
  formulæ will work for amenable sets such as N". Fix: for S-amenable sets
  (amenable plus S(x) ∈ V for x ∈ M), Sat is uniformly Δ^M_1 (WS p. 63).
- Claim on p. 66: "The discussion on page 66 seems to suggest that any
  statement which is Σ^KPI_1 is Σ1 over any Lλ for limit λ > ω, but such is of
  course not the case: consider the statement 'there are at least three limit
  ordinals'."

### 2.4 Errors in Chapter VI, section 1 (WS pp. 63-64)

- Lemma VI.1.13 "SatA is Δ^BS_1": FALSE, "being a generalisation of the false
  Lemma I.9.10."
- Lemma VI.1.14 "truth for Δ0 wffs is uniformly Σ1 for transitive rud-closed
  structures <M, A>": "This ought to be correct, and it is of the greatest
  importance." But Devlin's proof is tainted:
  - p. 242, the displayed formula is incomplete, 't' does not occur on the
    right-hand side; add f(Dom(f) - 1) = t.
  - p. 242, a bracket/object-language confusion in f(i) = F̊0(f(j), f(k)) ...
  - p. 242, line -7, a typo (tφ should be tψ; the PDF glyphs are degraded, WS
    prints "tϕ should be tϕ").
  - p. 243, "some correction will be needed as the troublemaker F∧ recurs here
    and appeal is made to the false Lemma I.9.3."
  - "The definition of G∃ oscillates between two and three variables."
  - p. 243, line -5, reference to 1.7 should perhaps be to 1.8.
- Taking stock (p. 64): "Much of the problem with Chapter I Section 9 has now
  been repaired, but the proposed definition of Sat is not possible in BS, and
  no other seems likely to succeed." "The proof given by Devlin [of VI.1.14] is
  tainted by its appeal to the false Lemma I.9.3, and therefore I propose in a
  sequel to rework the proof." (The sequel is MB section 9, see
  rudimentary-functions.md section 4.2.)

## 3. The cures (WS pp. 64-66)

WS 10.24 (p. 66), verbatim:

> In the Introduction we spoke of three systems that might work in place of BS.
> One is our suggestion DS; the second is GJI, which apart from the restraint to
> Π1 foundation, is the system RUD discussed in Stanley's review: but we see now
> that there is a third system, a subsystem of both those; namely the system DBI
> + ∀a∀k∈ω [a]^k ∈ V, which proves Theorem 2.93, is a proper subsystem of GJI
> and a proper extension of DBI.

Concretely (WS pp. 64-65):

- DS = S0 + Δ0 separation + Π1 foundation + ω ∈ V + S(x) ∈ V. In DS: F∧ is
  Δ^{DS}_{0,S} (10.13, since in DS the graph of each partial recursive function
  is a set, Corollary 8.16); Build is Δ^{DS}_{0,S} (10.14); (DS) ∀a <ω a ∈ V
  (10.15); (DS) I.9.5 (10.16); (DS) w(u,φ) ∈ V (10.17); Sat(u,φ) is Δ^{DS}_1
  (10.18).
- GJI: (GJ) ∀n∈ω ∀a ∃u Seq(u, a, n) (10.19, via Π1 foundation); (GJ) I.9.5
  (10.20); (GJI) w(u,φ) ∈ V (10.21, using Theorem 2.93); "The LST formula
  Sat(u, φ) is Δ^{GJI}_1" (10.23). WS 10.22 REMARK: the natural proof of
  Devlin's I.9.6 would use Π2 foundation; provable in GJ but, by Model M7, not
  in DB.
- The third system: DBI + ∀a∀k∈ω [a]^k ∈ V (10.24).

WS 10.25 REMARK (p. 66), verbatim:

> I cannot claim to have checked through the whole book, but my remarks reassure
> me, if no-one else, that the errors are not catastrophic. A small change to
> the meaning of BS and all seems to be well.

## 4. The BS failure in MB (corroboration)

MB 1.45-1.48 (p. 11): "If we add the axiom of infinity plus the scheme of
foundation for all classes to DB we obtain the system BS as formulated on page
36 of Devlin's book Constructibility: BS = ReS0 + Cartesian product + full
foundation + ω ∈ V. The system BS is used extensively by Devlin in his study
[De] of constructibility: for each limit ordinal ζ the set Lζ in Gödel's
constructible hierarchy models BS. But counterexamples of Solovay show that it
is not quite strong enough for its intended tasks, one of which was to give a
definition of the truth predicate |=u φ..."

MB 1.46 (p. 11), verbatim:

> Model 6 of [M3, §5], where the defects of BS are discussed in detail, shows
> that although BS can prove the existence of [ω]1 and [ω]2 it cannot prove the
> existence of [ω]3, or indeed any [ω]k for k > 2. Thus BS is unable to form
> the set Sϑ and hence cannot define |=.

MB 1.47: MW is finitely axiomatisable "modulo one subtlety" (truth for Δ̇0 wffs
quantified in the language of discourse). MB 1.48: in Model 7 of [M3, §5], MW is
true but for some a, union{a} is absent.

MB p. 11 ("The systems DB, BS and MW"): DB0 = extensionality + nine set-
existence axioms (∅ ∈ V; {x,y} ∈ V; x \ y ∈ V; union x ∈ V; x ∩ {(x,y)2 | x ∈
y} ∈ V; Dom(x) ∈ V; {(y,x,z)3 | (x,y,z)3 ∈ b} ∈ V; x × y ∈ V; {(y,z,x)3 |
(x,y,z)3 ∈ c} ∈ V); DB = DB0 + Π1 foundation; DBI = DB + ω ∈ V; MW = DBI +
∀a∀k∈ω [a]^k ∈ V.

## 5. Do-not-repeat checklist (distilled)

For the rud-route formalization, each item below is a concrete error class with
its source:

1. Do not claim Δ0-ness for concatenation or F∧ without an addition-attempt
   mechanism; F∧ is Δ^BS_1, not Δ0 (WS 10.3, Lemma 9.3).
2. Do not quantify over all finite sequences of unbounded length in a weak
   system; Seq needs S(x) or [a]^k machinery (WS 9.5, 10.5, 10.6; MB 1.46).
3. Do not let Build admit non-subformula junk; require a minimality condition
   (WS p. 59, "Definition of Build").
4. Do not assume w(u, φ) (names of members of u) is a set for infinite u; the
   Sat definition cannot be repaired inside BS (WS p. 62, Lemma 9.10).
5. Do not conflate the two definitions of "Σ0 function" (class term vs
   pointwise-with-transitive-M); they are equivalent only when TCo holds
   (WS 10.1).
6. Do not conflate (X × X) × X with X × (X × X) when the ambient theory is
   weak; they are provably different in models of BS (WS 10.0).
7. Do not claim uniform Δ1 truth for amenable sets; uniform Δ^M_1 truth for Sat
   requires S-amenability (WS pp. 62-63, 10.12).
8. Do not reuse Lemma 9.3 inside the VI.1.14 proof; rework the Δ0-truth proof
   independently (WS p. 64; the rework is MB section 9).
9. Watch variable/arity slips of the Devlin type: 'n' for 'm' in A(x); G∃ with
   two vs three variables; reference 1.7 vs 1.8; F∈ vs F∃ (WS pp. 59-64).
10. Cite the Stanley review correctly: JSL 52(3), 1987, 864-867, not 53 (MB
    and WS bibliographies both slip).
11. A transitive-closure existence claim in a weak system needs proof: "the
    transitive closure of any set exists" is not provable even in Zermelo's
    set theory (SZ footnote 3, p. 9, explicitly flagging "a claim made in
    [1]" = Devlin); WS section 12 gives a model of Z + full foundation in
    which TCo fails (WS 12.7 THEOREM: "K is a supertransitive model of Zermelo
    set theory Z in which some set is a member of no transitive set").

## 6. Source-consumption map

- WS section 10: primary inventory (sections 2-4).
- WS sections 5-6, 12: the models used as witnesses (Model 5, 6, 7, 9, M6,5;
  K).
- MB 1.45-1.48: corroboration (section 4).
- SZ footnote 3: the TCo error class (section 5 item 11).
- W p. 1: Stanley's suggested cure (section 1).
