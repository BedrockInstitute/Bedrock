# Bell 2005: searchable PDF text extraction

Local PDF: [bell-2005-boolean-valued-models.pdf](bell-2005-boolean-valued-models.pdf).

Source: John L. Bell, Set Theory: Boolean-Valued Models and Independence Proofs, third edition, Oxford University Press, 2005. User-supplied PDF; source text, not Bedrock-authored prose.

PDF SHA-256: b90111f380286579104faeaa5c34bb5fd6b4bef071d4eb831f880f17d7f15082

Extraction: PyMuPDF 1.26.5; 211 PDF pages. All page text is retained in extraction order, with common typographic ligatures expanded for grep and trailing line whitespace removed. No mathematical reconstruction or paragraph rewriting. Unmapped control glyphs are escaped as [PDF-GLYPH-U+XXXX], not guessed. Superscripts, subscripts, accents and display-math reading order may be damaged. Consult the PDF before relying on exact formulas. PDF page 1 has no text layer. Printed Arabic page n corresponds to PDF page n+20, starting with printed page 1 at PDF page 21. Front-matter order is the source PDF order.

Search examples: `rg -n 'Maximum Principle|complete embedding|generic' dev/literature/bell-2005-boolean-valued-models.fulltext.md`; use `rg -n -U` for phrases crossing line breaks. The page headings and source theorem numbers are the citation locators. This is a retrieval artifact, not a fully corrected mathematical transcription.

## PDF page 001 | front matter

```text
[NO EXTRACTABLE TEXT ON THIS PAGE]
[Cover title transcription, visually checked]
OXFORD LOGIC GUIDES · 47
Set Theory
Boolean-Valued Models and Independence Proofs
THIRD EDITION
JOHN L. BELL
OXFORD SCIENCE PUBLICATIONS
```

## PDF page 002 | front matter

```text
OXFORD LOGIC GUIDES: 47
General Editors
ANGUS MACINTYRE
DOV M. GABBAY
DANA SCOTT

```

## PDF page 003 | front matter

```text
OXFORD LOGIC GUIDES
10. Michael Hallett: Cantorian set theory and limitation of size
17. Stewart Shapiro: Foundations without foundationalism
18. John P. Cleave: A study of logics
21. C. McLarty: Elementary categories, elementary toposes
22. R.M. Smullyan: Recursion theory for metamathematics
23. Peter Clote and Jan Kraj´ıcek: Arithmetic, proof theory, and computational complexity
24. A. Tarski: Introduction to logic and to the methodology of deductive sciences
25. G. Malinowski: Many valued logics
26. Alexandre Borovik and Ali Nesin: Groups of finite Morley rank
27. R.M. Smullyan: Diagonalization and self-reference
28. Dov M. Gabbay, Ian Hodkinson, and Mark Reynolds: Temporal logic: Mathematical
foundations and computational aspects, volume 1
29. Saharon Shelah: Cardinal arithmetic
30. Erik Sandewall:
Features and fluents:
Volume I: A systematic approach to the
representation of knowledge about dynamical systems
31. T.E. Forster: Set theory with a universal set: Exploring an untyped universe, second
edition
32. Anand Pillay: Geometric stability theory
33. Dov M. Gabbay: Labelled deductive systems
35. Alexander Chagrov and Michael Zakharyaschev: Modal logic
36. G. Sambin and J. Smith: Twenty-five years of Martin-L¨of constructive type theory
37. Mar´ıa Manzano: Model theory
38. Dov M. Gabbay: Fibring logics
39. Michael Dummett: Elements of intuitionism, second edition
40. D.M. Gabbay, M.A. Reynolds and M. Finger: Temporal logic: Mathematical foundations
and computational aspects, volume 2
41. J.M. Dunn and G. Hardegree: Algebraic methods in philosophical logic
42. H. Rott: Change, choice and inference: A study of belief revision and nonmonotoic
reasoning
43. Johnstone: Sketches of an elephant: A topos theory compendium, volume 1
44. Johnstone: Sketches of an elephant: A topos theory compendium, volume 2
45. David J. Pym and Eike Ritter: Reductive logic and proof search: Proof theory, semantics
and control
46. D.M. Gabbay and L. Maksimova: Interpolation and definability: modal and intuitionistic
logics
47. John L. Bell: Set theory: Boolean-valued models and independence proofs, third edition

```

## PDF page 004 | front matter

```text
Set Theory
Boolean-valued Models and
Independence Proofs
Third Edition
JOHN L. BELL
Professor of Philosophy
University of Western Ontario
CLARENDON PRESS
• OXFORD
2005

```

## PDF page 005 | front matter

```text
3
Great Clarendon Street, Oxford OX2 6DP
Oxford University Press is a department of the University of Oxford.
It furthers the University’s objective of excellence in research, scholarship,
and education by publishing worldwide in
Oxford New York
Auckland Cape Town Dar es Salaam Hong Kong Karachi
Kuala Lumpur Madrid Melbourne Mexico City Nairobi
New Delhi Shanghai Taipei Toronto
With offices in
Argentina Austria Brazil Chile Czech Republic France Greece
Guatemala Hungary Italy Japan Poland Portugal Singapore
South Korea Switzerland Thailand Turkey Ukraine Vietnam
Oxford is a registered trade mark of Oxford University Press
in the UK and in certain other countries
Published in the United States
by Oxford University Press Inc., New York
c⃝John L. Bell, 2005
The moral rights of the author have been asserted
Database right Oxford University Press (maker)
First published 2005
All rights reserved. No part of this publication may be reproduced,
stored in a retrieval system, or transmitted, in any form or by any means,
without the prior permission in writing of Oxford University Press,
or as expressly permitted by law, or under terms agreed with the appropriate
reprographics rights organization. Enquiries concerning reproduction
outside the scope of the above should be sent to the Rights Department,
Oxford University Press, at the address above
You must not circulate this book in any other binding or cover
and you must impose the same condition on any acquirer
British Library Cataloguing in Publication Data
Data available
Library of Congress Cataloging in Publication Data
Data available
Typeset by Newgen Imaging Systems (P) Ltd., Chennai, India
Printed in Great Britain
on acid-free paper by
Biddles Ltd., King’s Lynn, Norfolk
ISBN 0–19–856852–5
978–0–19–856852–0 (Pbk.)
1 3 5 7 9 10 8 6 4 2

```

## PDF page 006 | front matter

```text
CONTENTS
List of Problems
xxi
0
Boolean and Heyting Algebras:
The Essentials
1
Lattices
1
Heyting and Boolean algebras
3
Filters, ideals, and homomorphisms
8
Representation theorems for distributive lattices
11
Connections with logic
12
1
Boolean-valued Models of
Set Theory: First Steps
16
Basic set theory
16
Construction of the model
20
Subalgebras and their models
29
Mixtures and the Maximum Principle
33
The truth of the axioms of set theory in V (B)
37
Ordinals and constructible sets in V (B)
45
Cardinals in V (B)
48
2
Forcing and Some Independence Proofs
55
The forcing relation
55
Independence of the axiom of constructibility and
the continuum hypothesis
60
Problems
66
3
Group Actions on V (B) and the Independence
of the Axiom of Choice
71
Group actions on V (B)
71
The independence of the existence of definable
well-orderings of Pω
74
Problems
75
The independence of the axiom of choice
78
4
Generic Ultrafilters and Transitive
Models of ZFC
88
Problems
101

```

## PDF page 007 | front matter

```text
xx
CONTENTS
5
Cardinal Collapsing, Boolean Isomorphism,
and Applications to the Theory of
Boolean Algebras
109
Cardinal collapsing
109
Boolean isomorphism and infinitary equivalence
112
Applications to the theory of Boolean algebras
116
6
Iterated Boolean Extensions, Martin’s Axiom, and
Souslin’s Hypothesis
120
Souslin’s hypothesis
120
The independence of SH
122
Martin’s axiom
125
Iterated Boolean extensions
128
Further results on Boolean algebras
137
The relative consistency of SH
142
Problems
146
7
Boolean-valued Analysis
149
Boolean-valued models built from measure algebras
149
Boolean-valued models built from algebras of projections
153
8
Intuitionistic Set Theory and Heyting-Algebra-Valued
Models
158
Intuitionistic Zermelo set theory
158
Intuitionistic Zermelo–Fraenkel set theory
163
Heyting-algebra-valued models
165
Forcing in Heyting-algebra-valued models and
independence in IZF
167
Appendix: Boolean and Heyting Algebra-Valued Models as
Categories
169
Categories and functors
169
Toposes
175
Boolean and Heyting algebra-valued models as toposes
179
Historical Notes
182
Bibliography
184
Index of Symbols
188
Index
189

```

## PDF page 008 | front matter

```text
LIST OF PROBLEMS
1.24
Σ1-formulas in V (B)
33
1.26
Further properties of mixtures
34
1.29
A variant of the Maximum Principle
36
1.30
The Maximum Principle is equivalent to the axiom
of choice
36
1.40
Definite sets
43
1.45
Boolean-valued ordinals
47
1.47
Boolean-valued constructible sets
48
1.53
The κ-chain condition
53
2.4
Boolean completions of nonrefined sets
57
2.14
Infinite distributive laws and V (B)
66
2.15
Infinite distributive laws and V (B) continued
67
2.16
Weak distributive laws and V (B)
67
2.17
κ-closure and V (B)
68
2.18
An important set of conditions
68
2.19
Consistency of 2ℵ0 = ℵ2 + ∀κ ≥ℵ1[2κ = κ+] with ZFC
69
2.20
A further relative consistency result
69
2.21
Consistency of GCH + Pω ⊆L + Pω1 ̸⊆L with ZFC
70
3.5
Another characterization of homogeneity
73
3.10
The Boolean-valued subset defined by a formula
75
3.11
Ordinal definable sets in V (B)
76
3.12
Complete homomorphisms
76
3.13
Ultrapowers as Boolean extensions
77
4.26
Truth in M (B)
101
4.27
Countably M-complete ultrafilters
101
4.28
Atoms in B
101
4.29
Atoms and M[U]
101
4.30
A trivial Boolean extension
102
4.31
A transitive model of ¬AC
102
4.32
The converse to Corollary 4.7 fails
102
4.33
Construction of uncountable transitive models of ZFC + V ̸= L
103
4.34
Generic sets of conditions
103
4.35
Canonical generic sets and the adjunction of maps
105
4.36
Adjunction of a subset of ω
105
4.37
Intermediate submodels and complete subalgebras
106

```

## PDF page 009 | front matter

```text
xxii
LIST OF PROBLEMS
4.38
Involutions and generic ultrafilters
107
4.39
The submodel of hereditarily ordinal definable sets
108
5.3
Pω ∩L can be countable
110
5.4
More on collapsing algebras
111
5.5
Consistency of CH and ¬CH with the existence of measurable
cardinals
111
5.16
Universal complete Boolean algebras
119
5.17
Homogeneous Boolean algebras
119
6.7
A stronger form of Martin’s axiom?
126
6.10
An isomorphism of Boolean algebras
128
6.35
The iteration theorem
146
6.36
More on ⊗
147
6.37
The operation inverse to ⊗
147
6.38
Injective Boolean algebras
147

```

## PDF page 010 | front matter

```text
NOTE TO THIRD EDITION
In this new edition the background material has been enlarged to include an
introduction to Heyting algebras, and chapters (also of an introductory nature)
added on Boolean-valued analysis and Heyting-algebra valued models of intui-
tionistic set theory. In a new Appendix the basic concepts of category theory are
outlined and Boolean and Heyting-algebra valued models presented from that
standpoint, affording important insights into the nature of these models.
1 July 2004
J.L.B.

```

## PDF page 011 | front matter

```text
PREFACE TO THE SECOND EDITION
The present book had its origin in lecture courses I gave at London University
during the early seventies. In writing it, my objective has been to provide a
systematic and adequately motivated account of the theory of Boolean-valued
models, deriving along the way the central set-theoretic independence proofs in
the particularly elegant form that the Boolean-valued approach enables them
to assume. The book is primarily intended for readers who have mastered the
material ordinarily dealt with in a first course on axiomatic set theory, including
constructible sets and the G¨odel relative consistency proofs. I have also assumed
some acquaintance with mathematical logic, Boolean algebras, and the rudi-
ments of general topology. In order to expand the scope of the book, and to
develop the reader’s skill in the subject, many problems (with hints for solution)
have been included, some of a more sophisticated character.
The chief purpose in preparing this second edition has been to incorporate an
account of iterated Boolean extensions and the consistency (and independence)
of Souslin’s hypothesis, material not included in the original edition. The addi-
tion of this new material (which appears in Chapter 6) necessitated that certain
changes be made in earlier chapters: this requirement, together with the generous
offer of the Oxford University Press to completely reset the book, afforded me
the opportunity of substantially modifying the original text. The major changes
in this regard include a new—and I believe more perspicuous—proof that the
axiom of choice holds in the model, and a revamping of Chapter 3 on the inde-
pendence of the axiom of choice in terms of group actions on the model. (I am
grateful to Yoshindo Suzuki for suggesting the idea of bringing group actions
into the foreground.) I have also grasped the opportunity of suppressing the
references with which the original text was liberally peppered, and whose some-
what misleading nature proved vexatious to several reviewers. These references
have now been replaced by a set of brief—but nevertheless, I hope, reasonably
accurate—historical notes at the end of the book.
It will be evident that in writing a book of this kind I have incurred a heavy
intellectual debt to the mathematicians whose work I have attempted—with
some temerity, perhaps—to expound. In this respect I am particularly indebted
to Dana Scott. His unpublished, but widely circulated, 1967 notes (Scott 1967)
are familiar to all set-theorists as the urtext in the field of Boolean-valued models
and their influence is to be observed throughout the book. Moreover, as Editor
of the Oxford Logic Guides he offered much advice and assistance during the

```

## PDF page 012 | front matter

```text
viii
PREFACE TO THE SECOND EDITION
preparation of the original text and has generously provided a Foreword. It was
at his suggestion that I embarked on the preparation of this new edition; I am
grateful to him both for his encouragement and for his offer to have the text set
at Carnegie-Mellon University using the formatting system TEX (which, as the
reader will see, has resulted in a most elegant printed text).
It is also a pleasure to tender my thanks to John Truss for his careful reading
of the manuscript of the original edition and his many ideas for improving it;
Enrique Hernandez for his assistance in checking the typescript; Gordon Monro
for his valuable comments on Chapter 6, which resulted in the eradication of
many errors; Karin Minio and members of the Computer Science Department at
Carnegie-Mellon University for their careful handling of the computer prepara-
tion of the text; and Mimi Bell and Buffy Fennelly for their expert typing of the
manuscript. Finally, I would record my gratitude to Anthony Watkinson and the
Oxford University Press, without whom the whole enterprise would never have
been brought to fruition.
London
June 1984

```

## PDF page 013 | front matter

```text
PREFACE TO THE FIRST EDITION
The present book had its origin in lecture courses I gave at London University
during 1972/3 and 1974/5. In writing it, my purpose has been to provide a
systematic and adequately motivated account of the theory of Boolean-valued
models, deriving along the way the basic set-theoretical independence proofs in
the particuarly elegant form they naturally assume in this approach. The book is
primarily intended for readers who have mastered the material ordinarily covered
in a first course on axiomatic set theory, including constructible sets and the
G¨odel relative consistency proofs. I have also assumed some acquaintance with
mathematical logic, Boolean algebras, and the rudiments of general topology.
In order to give the book wider scope, and to develop the reader’s skill in the
subject, many problems (with hints for solution) have been included, some of a
more sophisticated character.
It will be evident from the many references and attributions given in the
text that I have incurred a heavy intellectual debt to the mathematicians whose
work I have attempted—with some temerity, perhaps—to expound here. In this
respect I am particularly indebted to Dana Scott. His unpublished, but widely
circulated, 1967 notes (Scott 1967) are familiar to all workers in the field of
Boolean-valued models and their influence is to be observed throughout the book.
Moreover, as Editor of the Oxford Logic Guides he offered much valuable advice
and assistance during the preparation of the text and has generously provided a
Foreword. I would also like to thank John Truss for reading the manuscript and
making many helpful suggestions for improving it, Enrique Hernandez for his
assistance in checking the typescript, and Buffy Fennelly for her expert typing.
Finally, a cautionary word on references to the Bibliography. In a subject
which has developed as rapidly as the one treated in this book, it is inevitable
that many results and notions never reach the stage of official publication in their
original form, but are instead quickly absorbed into that nebulous domain com-
monly known among mathematicians as ‘folklore’. (See Dana Scott’s Foreword
for an illuminating discussion of the background and growth of the subject.)
Accordingly, the reader should be warned that the bibliographical references in
the text are not necessarily to original sources, but rather indicate the places
from which I have drawn my material.
London
J.B.
June 1977

```

## PDF page 014 | front matter

```text
FOREWORD
Even if we were not required by Russell’s Paradox to take care in formulating
the axioms of set theory, we would nevertheless have many difficult questions to
answer concerning infinite combinatorics and infinite cardinal numbers. Think
for a moment of the Axiom of Choice, the Continuum Hypothesis, Souslin’s
Hypothesis, the questions of the existence of inaccessible and measurable car-
dinals, the problems of the Lebesgue measurability of projective sets, or of the
determinateness of various kinds of infinite games. These are all questions of
‘na¨ıve’ set theory, many involving little beyond the concept of the arbitrary set
of real numbers. Perhaps it is only hindsight (helped on, to be sure, by G¨odel’s
Incompleteness Theorem), but we would have been extraordinarily lucky if these
intricate and often fundamental problems were capable of being settled by logic
alone. By ‘logic’ here we mean first-order logic (the logic of connectives and quan-
tifiers) together with some rather pure ‘ontological’ axioms of set existence (like
the Comprehension Axiom). An axiom like the Extensionality Axiom, which says
that sets are uniquely determined by their elements, is also sufficiently logical in
character, because of its almost definitional nature. So we can throw it to the
side of logic.
When we come to the Axiom of Choice, we begin to waver: it might be argued
that it is implicit in the concept of the totally arbitrary set. On the other hand,
there could be other notions of what it means to determine a set for which it
would fail; thus, the act of assuming it is indeed axiomatic: it is ‘self-evident’
but not just a matter of logic. But then, perhaps it is a matter of logic after all,
because the finite version is provable. In other words, first-order logic is strong
enough for some conclusions, but it is in general too weak: we ought perhaps to
allow ‘infinitary’ inferences also. And at this point we begin to wonder what is
meant by logic. It would seem rather circular if in making set theory precise, we
had to use set theory in order to make logic precise.
With regard to the Continuum Hypothesis most people, I feel, would call
this assumption truly axiomatic, since it is so very special in excluding certain
sets of reals of an intermediate cardinality. True, it can be stated in rather pure
terms, and in second-order formulations of set theory it would be decided: only
we cannot know which way. Thus, the argument for its logical character is rather
thin. Certainly G¨odel’s consistency proof gives us no real evidence. Beautiful as
they are, his so-called constructible sets are very special being almost minimal in
satisfying formal axioms in a first-order language. They just do not capture the

```

## PDF page 015 | front matter

```text
xiv
FOREWORD
notion of set in general (and they were not meant to). The constructible universe
is extremely interesting in itself (e.g. Jensen showed, among other things, that
Souslin’s Hypothesis fails if V = L), but there are very few who would want to
assume V = L once and for all. This leaves us more than ever with unsettled
feelings as to where to draw the line between mathematics and logic.
The events in set theory since 1960 have in some ways made matters even
worse. First there was the explosion in large cardinals beginning with the Hanf-
Tarski discovery that the first inaccessible (already large enough for a cardinal)
was much smaller than the first measurable. There was then a most elaborate
development in the study of infinite combinatorics by a large number of research-
ers too numerous to mention here, but among whom Erd¨os has a central place.
On the logical side these results had many model-theoretic consequences and
in particular showed that the spectrum of stronger and stronger large-cardinal
axioms was very finely divided. (The reader can refer to Drake (1974) for a
survey.) And the work still goes on. Perhaps this sort of study is not basically
disturbing, however, for it just shows—in nearly linear order—that if you want
more you have to assume more. It did turn out that the existence of measurable
cardinals was inconsistent with V = L, but so much the worse for the ‘unnatural’
constructible sets. And some comfort can be gained from the fact that any num-
ber of attempts at showing that measurable cardinals do not exist have failed
even though much cleverness was expended.
It was in 1963 that we were hit by a real bomb, however, when Paul
J. Cohen discovered his method of ‘forcing’, which started a long chain reaction
of independence results stemming from his initial proof of the independence of
the Continuum Hypothesis. Set theory could never be the same after Cohen, and
there is simply no comparison whatsoever in the sophistication of our knowledge
about models for set theory today as contrasted to the pre-Cohen era. One of the
most striking consequences of his work is the realization of the extreme relativity
of the notion of cardinal number. G¨odel has shown that, by cutting down on
the totality of sets, the cardinals (of the model L) would be very well-behaved.
Cohen showed that by expanding the totality of sets the cardinals would be very
ill-behaved. (Tiresomely difficult questions about the possible bad behaviour
of singular cardinals from model to model is more than sufficient to make the
point.) Of course we had realized that the cardinals of L might not be the cardin-
als of V (indeed, with fewer sets there are more cardinals, because there is less
chance for a one–one correspondence), but we had no idea before Cohen (and
those who so quickly jumped into the field after him) how much independence
there could be. Thus we can make (if anyone would want to) 2ℵ0 = ℵ17 and
2ℵ1 = ℵ2001 in some model or the other, and even with these silly choices the
size of 2ℵ2 is not at all well determined (except that it has to be greater or equal
to ℵ2001 and has to avoid certain singular cardinals).
Cohen’s achievement lies in being able to expand models (countable, standard
models) by adding new sets in a very economical fashion: they more or less have
only the properties they are forced to have by the axioms (or by the truths

```

## PDF page 016 | front matter

```text
FOREWORD
xv
of the given model). I knew almost all the set-theoreticians of the day, and I
think I can say that no one could have guessed that the proof would have gone
in just this way. Model-theoretic methods had shown us how many nonstandard
models there were; but Cohen, starting from very primitive first principles, found
the way to keep the models standard (that is, with a well-ordered collection of
ordinals). And moreover his method was very flexible in introducing lots and lots
of models—indeed, too many models. Is it not just a bit embarrassing that the
currently accepted axioms for set theory (which could be given—as far as they
went—a perfectly natural motivation) simply did not determine the concept of
infinite set even in the very important region of the continuum?
We should not get the idea that Cohen’s method solves all problems. For
example, Shoenfield’s Absoluteness Lemma shows us why the ‘simplest’ noncon-
structible set is ∆1
3, and thus Cohen’s models can only start their independence
proofs at that level of the analytic hierarchy. Furthermore, we as yet have no
exactly similar model-theoretic independence proofs from V = L, and this is cer-
tainly a very interesting problem.1 Nevertheless, Cohen’s ideas created so many
proofs that he himself was convinced that the formalist position in foundations
was the rational conclusion. I myself cannot agree, however. I see that there are
any number of contradictory set theories, all extending the Zermelo–Fraenkel
axioms: but the models are all just models of the first-order axioms, and first-
order logic is weak. I still feel that it ought to be possible to have strong axioms,
which would generate these types of models as submodels of the universe, but
where the universe can be thought of as something absolute. Perhaps we would
be pushed in the end to say that all sets are countable (and that the continuum
is not even a set) when at last all cardinals are absolutely destroyed. But really
pleasant axioms have not been produced by me or anyone else, and the sugges-
tion remains speculation. A new idea (or point of view) is needed, and in the
meantime all we can do is to study the great variety of models. It is the pur-
pose of the present book to give an introduction to this study via the notion of
Boolean-valued models. Chapter 2, however, ties up the approach with Cohen’s
original ideas, though avoiding the technicalities of the ramified languages as is
usual in most later presentations.
The idea of using Boolean-valued models to describe forcing was discovered
by Solovay in 1965. He was using Borel sets of positive measure as forcing con-
ditions; the complications of seeing just what was true in his model led him,
as I remember from a conversation at Stanford around September of that year,
to summarize various calculations by saying that the combination of conditions
forcing a statement added up to the ‘value’ of that statement (cf. Theorem 2.4 in
1Recently, however, Harvey Friedman in his paper ‘On the necessary use of abstract set
theory’, Advances in Mathematics, vol. 4l, 1981, pp. 209–280, showed that interesting combin-
atorial propositions about Borel functions are independent even from V = L. His methods use
nonstandard models in a way he considers essential. It does not seem that the method can be
called similar to Cohen’s, however, and there seem to be good reasons for this difference.

```

## PDF page 017 | front matter

```text
xvi
FOREWORD
this book and the surrounding discussion). Petr Vopˇenka (1965) independently
had much the same idea, but his initial presentation was brief and not so very
attractive; so we were not much struck by his approach at first. In thinking over
Solovay’s suggestion, it occurred to me that by starting with Boolean-valued
sets from the very beginning, many of the more tedious details of Cohen’s ori-
ginal construction of the model were avoided. Solovay by November of 1965
had also come to this conclusion himself, and, as it turned out, this was what
Vopˇenka was actually doing. In the end, as was demonstrated by the paper of
Shoenfield (1971) from the 1967 Set Theory Symposium, there is very little to
choose between the methods: forcing and Boolean-valued models both come to
the same thing. Psychologically, however, one attitude or the other may be more
suggestive. Boolean-valued models are quite natural; but, when it comes to the
proofs (and the construction of the right model), one often has to look very
closely at the forcing conditions.
The whole history of the independence proofs is rather complex and it could
only be made clear by going into the exact technical details. The two volumes of
contributions to the 1967 Symposium (Scott 1971; Jech 1974) contain many of
the original papers by Cohen and an historical paper on the Prague School by
Petr Hajek. The lecture notes by Felgner (1971) also contain a very useful sum-
mary of basic results with many references to the original sources. In the present
book, John Bell has made very good use of the lecture notes on Boolean-valued
models, which were distributed at the Symposium, and which were prepared for
typing by Kenneth Bowen and myself during the time of the conference from
my handwritten manuscript. These are the notes (Scott 1967) mentioned in the
bibliography; in writing them my main role was that of an expositor.
There are many references in the literature to the Scott–Solovay paper, which
was to be published as an expanded version of the 1967 notes. This paper does
not exist, and it is my own personal failing for not putting it together from the
materials I had at hand. I discussed it several times with Robert Solovay, but
we were not at the same institution and could not work very closely together.
He drafted parts of certain sections, but he was working on so many papers at
the same time that he did not have the opportunity to draft the whole paper.
The present book essentially supplants the projected Scott–Solovay paper. Part
of my own difficulty about writing the Scott–Solovay paper was the fantastic
growth of the field and the speed with which it changed. During the winter of
1968–1969 I became profoundly discouraged because I felt unable to make any
original contributions: any ideas I had were either wrong or already known. It
is easy enough to say now that I should have been content to be a reporter and
expositor, but, at the very moment when one is being left behind, things seem
less pleasant. I put these remarks forward not as an excuse but simply as an
explanation of why I could not complete what I set out to do.
Looking back on the development of logic and set theory it is very tempting
to ask why the independence proofs were not discovered earlier. From the point
of view of Boolean algebras we had the needed technical expertise in constructing

```

## PDF page 018 | front matter

```text
FOREWORD
xvii
complete Boolean algebras many years before Cohen. Perhaps model theory up to
1960 had concentrated too much on first-order theories. Actually in September of
1951, in a paper of Alonzo Church delivered at the Mexican Scientific Conference,
a suggestion for Boolean-valued models of type theory had already been made.2
However, the suggestion suffered from the fault that not enough care was taken
over the Axiom of Extensionality, since Church recommends that at higher types
one take all functions from one type to the other. Unless the equality relation and
membership (application) is treated as on p. 23 of the present book, difficulties
will arise. These difficulties would have been easily overcome, though, if anyone
had tried to develop this clearly stated suggestion.
The ‘first-order disease’ is most plainly seen in the book by Rasiowa and
Sikorski (1963). They had for a number of years considered Boolean-valued mod-
els of first-order sentences (as had Tarski, Mostowski, Halmos, and many others
working on algebraic logic). Unfortunately they spent most of the time con-
sidering logical validity (truth in all models) rather than the construction of
possibly interesting particular models. But even so, with all this machinery, no
one thought to ask: how do we interpret second-order quantifiers? It would have
been the most natural thing in the logical world, because the values of sentences
with arbitrary Boolean-valued relations were already defined. The step from the
arbitrary constant, to the variable, to the quantifier is obvious: it had already
been taken at the first-order level. It was a real opportunity missed, and one
missed for no good reason except the failure to ask the right question. And, if
the question had been asked, the problems about cardinalities would have had
to be faced. Well, there is no changing of history.
What about forcing? How new was this idea? As we have said, the application
to set theory was strikingly new. Kleene, however, had already used a similar
idea in recursion theory where, in studying degrees, he had to force a sequence
of [PDF-GLYPH-U+0001]0
1-sentences. The wider model-theoretic significance was not appreciated,
though, even if the technique was generalized in recursion theory. In studies of
intuitionistic logic (both with Kripke models and with Beth models) the kinds of
clauses similar to the forcing definition were quite well-known, but it did not seem
to occur to anyone to employ intuitionistic logic in making extensions of models.
Kreisel, in a paper at the Infinitistic Methods Conference in Warsaw in 1959,
suggested briefly something very like forcing, but the plan lay quite undeveloped
by him or any of his readers. However, after Cohen’s original announcement,
I pointed out the analogy with intuitionistic interpretations, and along these
lines Cohen simplified his treatment of negation at my suggestion. Later the
intuitionistic analogy was taken up more seriously by Grzegorczyk and worked
out in detail in the book by Fitting (1969). What has transpired since that time
is that the set theory in intuitionistic logic proper (not in the double-negative,
2The paper was published in English in Boletin de la Sociedad Matematica Mexicana,
vol. 10, 1953, pp. 41–52, under the title ‘Non-normal truth-tables for the prepositional calculus’.
The remark Church attributes to Lagerstr¨om.

```

## PDF page 019 | front matter

```text
xviii
FOREWORD
weak-forcing format) has become much more interesting, owing chiefly to the
work in category theory by Lawvere and Tierney on topoi. Not only are there
Heyting-valued models, but there are many more abstract ‘sheaf’ models. This is,
however, a topic for quite another book, since these new models in intuitionistic
logic have not as yet resulted in new independence proofs in classical set theory.
I think we can look forward to some new insights in this direction, nevertheless,
when the more abstract models are better understood.
Oxford
Dana Scott
May 1977
(Revised, Pittsburgh, August 1984)

```

## PDF page 020 | front matter

```text
To Mimi

```

## PDF page 021 | printed page 1

```text
0
BOOLEAN AND HEYTING ALGEBRAS:
THE ESSENTIALS
In this book we shall make considerable use of the theory of Boolean algebras. In
the book’s later sections we shall also employ the concept of Heyting algebra. We
begin with a brief account of these notions. Fuller accounts include Balbes and
Dwinger (1974), Bell and Machover (1977), Halmos (1963), Johnstone (1982),
and Sikorski (1964).
Lattices
A lattice is a (nonempty) partially ordered set L with partial ordering ≤in which
each two-element subset {x, y} has a supremum or join—denoted by x ∨y—and
an infimum or meet—denoted by x ∧y. A top (bottom) element of a lattice L is
an element, denoted by 1L(0L) such that x ≤1L(0L ≤x) for all x ∈L. When
confusion is unlikely we drop the subscript and write simply 1 or 0. A lattice with
top and bottom elements is called bounded. A lattice is trivial if it contains just
one element, or equivalently, if in it 0 = 1. A sublattice of a bounded lattice L is
a subset of L containing 0 and 1 and closed under Ls meet and join operations.
It is easy to show that the following hold in any bounded lattice:
x ∨0 = x,
x ∧1 = x,
x ∨x = x,
x ∧x = x,
x ∨y = y ∨x,
x ∧y = y ∧x,
x ∨(y ∨z) = (x ∨y) ∨z,
x ∧(y ∧z) = (x ∧y) ∧z,
(x ∨y) ∧y = y,
(x ∧y) ∨y = y.
Conversely, suppose that (L, ∨, ∧, 0, 1) is an algebraic structure, with ∨, ∧binary
operations, in which the above equations hold, and define the relation ≤on L
by x ≤y iffx ∨y = y. It is then easily shown that (L, ≤) is a bounded lattice in
which ∨and ∧are, respectively, the join and meet operations, and 1 and 0 the
top and bottom elements. This is the equational characterization of lattices.
Examples (i) Any linearly ordered set is a lattice; clearly in this case we have
x ∧y = min(x, y) and x ∨y = max(x, y).
(ii) For any set X, the power set PA is a lattice under the partial ordering
of set inclusion. In this lattice X ∨Y = X ∪Y and X ∧Y = X ∩Y . A sublattice
of a power set lattice is called a lattice of sets.

```

## PDF page 022 | printed page 2

```text
2
BOOLEAN AND HEYTING ALGEBRAS
(iii) If X is a topological space, the families O(X) and C(X) of open sets
and closed sets, respectively, in X each form a lattice under the partial ordering
of set inclusion. In these lattices ∨and ∧are the same as in Example (ii).
A lattice is said to be distributive if the following identities are satisfied:
x ∧(y ∨z) = (x ∧y) ∨(x ∧z),
x ∨(y ∧z) = (x ∨y) ∧(x ∨z).
Interestingly, each of these conditions implies the other. For example, assuming
the first condition, we have:
(x ∨y) ∧(x ∨z) = [x ∧(x ∨z)] ∧[y ∧(x ∨z)]
= x ∨[(y ∧x) ∨(y ∧z)]
= [x ∨(y ∧x)] ∨(y ∧z)
= x ∨(y ∧z).
The converse is proved similarly.
In the sequel by the term ‘distributive lattice’ we shall understand ‘bounded
distributive lattice’.
An easy inductive argument shows that any nonempty finite subset
{x1, . . . , xn} of a lattice has a supremum, or join, and an infimum, or meet:
these are denoted respectively by x1 ∨· · ·∨xn, x1 ∧· · ·∧xn. An arbitrary subset
of a lattice need not have an infimum or a supremum: for example, the set of
even integers in the totally ordered lattice of integers has neither. If a subset X
of a given lattice does possess an infimum, or meet, it is denoted by [PDF-GLYPH-U+0002] X; if the
subset possesses a supremum, or join, it is denoted by [PDF-GLYPH-U+0003] X. When X is given
in the form of an indexed set {xi: i ∈I}, its join and meet, if they exist, are
written respectively [PDF-GLYPH-U+0003]
i∈I xi and [PDF-GLYPH-U+0002]
i∈I xi.
A lattice is complete if every subset has an infimum and a supremum. The
meet and join of the empty subset of a complete lattice are, respectively, its top
and bottom elements. It is a curious fact that, for a lattice to be complete, it
suffices that every subset have a supremum, or every subset an infimum. For the
supremum (infimum), if it exists, of the set of lower (upper)1 bounds of a given
subset X is easily seen to be the infimum (supremum) of X.
Examples (i) The power set lattice PA of a set A is a complete lattice
in which joins and meets coincide with set-theoretic unions and intersections
respectively.
(ii) The lattices O(X) and C(X) of open sets and closed sets of a topological
space are both complete. In O(X) the join and meet of a subfamily {Ui : i ∈I}
1Here by a lower (upper) bound of a subset X of a partially ordered set P we mean an
element a ∈P for which a ≤x(x ≤a) for every x ∈X.

```

## PDF page 023 | printed page 3

```text
HEYTING AND BOOLEAN ALGEBRAS
3
are given by
[PDF-GLYPH-U+0004]
i∈I
Ui =
[PDF-GLYPH-U+0005]
i∈I
Ui
[PDF-GLYPH-U+0006]
i∈I
Ui =
◦
(
[PDF-GLYPH-U+0007]
i∈I
Ui .
In C(X) the join and meet of a subfamily {Ai : i ∈I} are given by
[PDF-GLYPH-U+0004]
i∈I
Ai =
[PDF-GLYPH-U+0005]
i∈I
Ai
[PDF-GLYPH-U+0006]
i∈I
Ai =
[PDF-GLYPH-U+0007]
i∈I
Ai.
Here
◦
A and A denote the interior and closure, respectively, of a subset A of a
topological space.
Heyting and Boolean algebras
A Heyting algebra is a bounded lattice (H, ≤) such that, for any pair of elements
x, y ∈H, the set of z ∈H satisfying z ∧x ≤y has a largest element. This
element, which is uniquely determined by x and y, is denoted by x ⇒y: thus
x ⇒y is characterized by the following condition: for all z ∈H,
z ≤x ⇒y if and only if z ∧x ≤y.
The binary operation on a Heyting algebra, which sends each pair of elements
x, y to the element x ⇒y is called implication; the operation, which sends each
element x to the element x∗= x ⇒0 is called pseudocomplementation. We also
define the operation ⇔of equivalence by x ⇔y = (x ⇒y) ∧(y ⇒x). These
operations are easily shown to satisfy:
x ⇒(y ⇒z) = (x ∧y) ⇒z,
x ⇒y = 1 ↔x ≤y,
x ⇔y = 1 ↔x = y,
y ≤z →(x ⇒y) ≤(x ⇒z),
x ∧(x ⇒y) ≤y
y ≤x∗↔y ∧x = 0 ↔x ≤y∗,
x ≤x∗∗,
x∗∗∗= x∗,
(x ∨y)∗= x∗∧y∗.
To establish the last of these, observe that
z ≤(x ∨y)∗↔z ∧(x ∨y) = 0
↔(z ∧x) ∨(z ∧y) = 0
↔z ∧x = 0 and z ∧y = 0
↔z ≤x∗and z ≤y∗
↔z ≤x∗∧y∗.

```

## PDF page 024 | printed page 4

```text
4
BOOLEAN AND HEYTING ALGEBRAS
Any Heyting algebra is a distributive lattice. To see this, calculate as follows
for arbitrary elements x, y, z, u:
x ∧(y ∨z) ≤u ↔y ∨z ≤x ⇒u
↔y ≤x ⇒u and z ≤x ⇒u
↔x ∧y ≤u and x ∧z ≤u
↔(x ∨y) ∧(x ∨z) ≤u.
Heyting algebras can also be characterized equationally. In fact we have the
Proposition 0.1 Let L be a bounded lattice, ⇒a binary operation on L. Then
⇒makes L into a Heyting algebra iffthe equations
(i) x ⇒x = 1
(ii) x ∧(x ⇒y) = x ∧y
(iii) y ∧(x ⇒y) = y
(iv) x ⇒(y ∧z) = (x ⇒y) ∧(x ⇒z)
are satisfied.
Proof Suppose the equations hold. First note that it follows immediately from
(iv) that the map x ⇒(−) is order preserving. Then if z ≤x ⇒y we have
z ∧x ≤x ∧(x ⇒y) = x ∧y ≤y.
Conversely, if z ∧x ≤y, then
z = z ∧(x ⇒z)
by (iii)
≤(x ⇒x) ∧(x ⇒z)
by (i)
= x ⇒(x ∧z)
by (iv)
≤x ⇒y
since x ⇒(−) is order preserving.
Conversely, suppose that L is a Heyting algebra. Since x∧z ≤z always holds,
it is clear that x ⇒x = 1. And since y ∧x ≤y, we have y ≤x ⇒y, that is,
y ∧(x ⇒y) = y. Now x ∧(x ⇒y) ≤y by definition, and x ∧(x ⇒y) ≤x, so
x∧(x ⇒y) ≤x∧y. But (x∧y)∧x ≤y, whence x∧y ≤x ⇒y, and x∧y ≤x, so
x ∧y ≤x ∧(x ⇒y). Hence x ∧(x ⇒y) = x ∧y. Finally, it is clear that x ⇒(−)
is order-preserving, so that x ⇒(y ∧z) ≤(x ⇒y) ∧(x ⇒z). But
(x ⇒y) ∧(x ⇒z) ∧x = [x ∧(x ⇒y)] ∧[x ∧(x ⇒z)]
≤y ∧z.
Hence (x ⇒y) ∧(x ⇒z) ≤x ⇒(y ∧z).

```

## PDF page 025 | printed page 5

```text
HEYTING AND BOOLEAN ALGEBRAS
5
Any linearly ordered set with top and bottom elements is a Heyting algebra
in which x ⇒y =
[PDF-GLYPH-U+0008]
1 if x ≤y
y if y < x.
A basic fact about complete Heyting algebras is that the following identity
holds in them:
(∗)
x ∧
[PDF-GLYPH-U+0004]
i∈I
yi =
[PDF-GLYPH-U+0004]
i∈I
x ∧yi.
And conversely, in any complete lattice satisfying (*), defining the operation ⇒
by x ⇒y = [PDF-GLYPH-U+0003]{z : z ∧x ≤y} turns it into a Heyting algebra.
To prove this, we observe that in any complete Heyting algebra,
x ∧
[PDF-GLYPH-U+0004]
i∈I
yi ≤z ↔
[PDF-GLYPH-U+0004]
i∈I
yi ≤x ⇒z
↔yi ≤x ⇒z, all i
↔yi ∧x ≤z, all i
↔
[PDF-GLYPH-U+0004]
i∈I
x ∧yi ≤z.
Conversely, if (*) is satisfied and x ⇒y is defined as above, then
(x ⇒y) ∧x ≤
[PDF-GLYPH-U+0004]
{z : z ∧x ≤y} ∧x =
[PDF-GLYPH-U+0004]
{z ∧x : z ∧x ≤y} ≤y.
So z ≤x ⇒y →z ∧x ≤(x ⇒y)∧x ≤y. The reverse inequality is an immediate
consequence of the definition.
In view of this result a complete Heyting algebra may also be defined to be
a complete lattice satisfying (*). Complete Heyting algebras are also known as
frames.
If X is a topological space, then the complete lattice O(X) of open sets in X
is a Heyting algebra. In O(X) meet and join are just set-theoretic intersection
and union, while the implication and pseudocomplementation operations are
given by
U ⇒V =
◦




(X −U) ∪V
and U ∗=
◦
[PDF-GLYPH-U+000C]
X −U.
A subalgebra of a Heyting algebra H is a sublattice of H, which is closed under
Hs implication operation. A subalgebra of O(X) for some topological space X
is called an algebra of opens.
Let L be a bounded lattice. A complement for an element a ∈L is an element
b ∈L satisfying a ∨b = 1 and a ∧b = 0. In general, an element of a lattice may

```

## PDF page 026 | printed page 6

```text
6
BOOLEAN AND HEYTING ALGEBRAS
have more than one complement, or none at all. However, in a distributive lattice
an element can have at most one complement. For if b, b′ are complements of an
element a of a distributive lattice, then a ∨b = a ∨b′ = 1 and a ∧b = a ∧b′ = 0.
From this we deduce
b = b ∨0 = b ∨(a ∧b′) = (b ∨a) ∧(b ∨b′) = 1 ∨(b ∨b′) = b ∨b′.
Similarly b′ = b ∨b′ so that b = b′.
In a Heyting algebra H the pseudocomplement a∗of an element a is not, in
general, a complement for a. (Consider the Heyting algebra of open sets of a
topological space.) But there is a simple necessary and sufficient condition on a
Heyting algebra for all pseudocomplements to be complements: this is stated in
the following.
Proposition
0.2 The following conditions on a Heyting algebra H are
equivalent:
(i) pseudocomplements are complements, that is, x ∨x∗= 1 for all x ∈H;
(ii) pseudocomplementation is of order 2, that is, x∗∗= x for all x ∈H.
Proof (i) →(ii). Assuming (i), we have
x∗∗= x∗∗∧1 = x∗∗∧(x ∨x∗)
= (x∗∗∧x) ∨(x∗∗∧x∗)
= (x∗∗∧x) ∨0 = (x∗∗∧x).
Therefore x∗∗≤x whence x∗∗= x.
(ii) →(i). We have (x ∨x∗)∗= x∗∧x∗∗= 0, so assuming (ii) gives x ∨x∗=
(x ∨x∗)∗∗= 0∗= 1.
We now define a Boolean algebra to be a Heyting algebra satisfying either
of the equivalent conditions, Proposition 0.2 (i) or (ii). The following identities
accordingly hold in any Boolean algebra:
x ∨y = y ∨x,
x ∧y = y ∧x
x ∨(y ∨z) = (x ∨y) ∨z,
x ∧(y ∧z) = (x ∧y) ∧z
(x ∨y) ∧y = y,
(x ∧y) ∨y = y
x ∧(y ∨z) = (x ∧y) ∨(x ∧z),
x ∨(y ∧z) = (x ∨y) ∧(x ∨z).
x ∨x∗= 1,
x ∧x∗= 0.
(x ∨y)∗= x∗∧y∗,
(x ∧y)∗= x∗∨y∗
x∗∗= x.

```

## PDF page 027 | printed page 7

```text
HEYTING AND BOOLEAN ALGEBRAS
7
It is easy to show that in any Boolean algebra x ⇒y = x∗∨y. In a complete
Boolean algebra we have the following identities:
[PDF-GLYPH-U+000D][PDF-GLYPH-U+0004]
i∈I
xi
[PDF-GLYPH-U+000E]∗
=
[PDF-GLYPH-U+0006]
i∈I
xi
∗,
[PDF-GLYPH-U+000D][PDF-GLYPH-U+0006]
i∈I
xi
[PDF-GLYPH-U+000E]
∗=
[PDF-GLYPH-U+0004]
i∈I
x∗
i ,
x ∧
[PDF-GLYPH-U+0004]
i∈I
yi =
[PDF-GLYPH-U+0004]
i∈I
(x ∧yi) ,
x ∨
[PDF-GLYPH-U+0006]
i∈I
yi =
[PDF-GLYPH-U+0006]
i∈I
(x ∨yi) .
Calling a lattice complemented if it is bounded and each of its elements
has a complement, we can characterize Boolean algebras alternatively as com-
plemented distributive lattices. For we have already shown that every Boolean
algebra is distributive and complemented. Conversely, given a complemented
distributive lattice L, write ac for the (unique) complement of an element
a; it is then easily shown that defining implication by x ⇒y = xc ∨y
turns L into a Heyting algebra in which x∗coincides with xc, so that L is
Boolean.
The meet, join, and complementation operations in a Boolean algebra are
called its Boolean operations. A subalgebra of a Boolean algebra B is a nonempty
subset closed under Bs Boolean operations. Clearly a subalgebra of a Boolean
algebra B is itself a Boolean algebra with the same top and bottom elements as
those of B.
Examples of Boolean algebras (i) The linearly ordered set 2 = {0, 1} with
0 < 1 is a complete Boolean algebra, the two-element algebra.
(ii) The power set lattice PA of any set A is a complete Boolean algebra.
A subalgebra of a power set algebra is called a field of sets.
(iii) Let F(A) consist of all finite subsets and all complements of finite subsets
of a set A. With the partial ordering of inclusion, F(A) is a field of sets called
the finite–cofinite algebra of A.
(iv) Let X be a topological space, and let C(X) be the family of all simul-
taneously closed and open (clopen) subsets of X. With the partial ordering of
inclusion, C(X) is a Boolean algebra called the clopen algebra of X.
(v) A subset U of a topological space X is said to be regular open2 if
◦
U =
U. The family RO(X) of all regular open subsets of X, partially ordered by
inclusion, is a complete Boolean algebra3—the regular open algebra of X—in
which 0 is ∅, 1 is X, and for U, V ∈RO(X), U ∨V =
◦
U ∪V , U ∧V = U ∩V
2In the Euclidean plane, regular open sets are those lacking ‘cracks’ or ‘pinholes’.
3For a proof of this, see, for example, Halmos 1963, section 7, Lemma 1.

```

## PDF page 028 | printed page 8

```text
8
BOOLEAN AND HEYTING ALGEBRAS
and U ∗= X −U. Moreover, for {Ui : i ∈I} ⊆RO(X),
[PDF-GLYPH-U+0004]
i∈I
Ui =
◦
[PDF-GLYPH-U+0005]
i∈I
Ui
[PDF-GLYPH-U+0006]
i∈I
Ui =
◦
[PDF-GLYPH-U+000C]
[PDF-GLYPH-U+0007]
i∈I
Ui .
An element a of a Heyting algebra H is said to be regular if a = a∗∗. A regular
open set in a topological space X is then precisely a regular element of O(X).
Clearly a Heyting algebra is a Boolean algebra if and only if each of its elements
is regular, so that O(X) is a Boolean algebra if and only if each of its open
subsets is regular open. In particular, if R is the space of real numbers with its
usual topology, O(R) is not a Boolean algebra.
Let B be the set of regular elements of H; it can be shown that B, with the
partial ordering inherited from H, is a Boolean algebra—the regularization of
H—in which the operations ∧and ∗coincide with those of H, but4 ∨B = (∨H)∗∗.
If H is complete, so is B; the operation [PDF-GLYPH-U+0002] in B coincides with that in H while
[PDF-GLYPH-U+0003]
B = ([PDF-GLYPH-U+0003]
H)∗∗.
It follows that the regular open algebra RO(X) coincides with the regulariz-
ation of O(X).
Filters, ideals, and homomorphisms
Let L be a (bounded) distributive lattice. A filter (ideal) in L is a subset F such
that 1 ∈F; 0 /∈F; x, y ∈F →x ∧y ∈F; x ∈F and x ≤y →y ∈F (resp.
0 ∈I; 1 ̸∈I; x, y ∈I →x ∨y ∈I; x ∈I and y ≤x →y ∈I.) Clearly a lattice
is trivial iffit contains no filters or ideals. A subset X of L has the finite meet
property (f.m.p) if the meet of any nonempty finite subset of X is ̸= 0. Clearly
any subset of a filter has the f.m.p.; conversely, any subset X having the f.m.p.
is included in a filter, namely
X+ = {y ∈L : ∃x1 ∈X . . . ∃xn ∈X[x1 ∧· · · ∧xn ≤y]}.
X+ is the least filter containing X—the filter generated by X. In particular for
a ̸= 0 the filter {a}+ = {x : a ≤x} is the least filter containing a; it is called the
principal filter generated by a.
A filter F in L is prime if it satisfies the condition x ∨y ∈F →x ∈F or
y ∈F: if L is a Boolean algebra, this is easily shown to be equivalent to the
condition ∀x[x ∈F or x∗∈F]. A filter maximal under inclusion is called an
ultrafilter. It is readily shown that a filter F is an ultrafilter iffit satisfies the
condition ∀x[∀y ∈F(x ∧y ̸= 0 →x ∈F]; in a Heyting algebra this condition is
equivalent to ∀x[x ∈F ∨x∗∈F]. It follows that, in a Boolean algebra, prime
4Here we write ∨B, ∨H for the join operations in B and H respectively, with similar
conventions employed below.

```

## PDF page 029 | printed page 9

```text
FILTERS, IDEALS, AND HOMOMORPHISMS
9
filters and ultrafilters coincide. Every ultrafilter in a distributive lattice is prime.
More generally, in a distributive lattice we have the
Proposition 0.3 Let F be a filter in a distributive lattice L, and b an element of
L such that b /∈F. Then there is a filter containing F maximal under inclusion
with respect to the property of not containing b. Any such filter is prime.
Proof The family F of filters in L containing F but not b is readily shown to be
closed under unions of chains, and so by Zorn’s lemma has a maximal element.
Let M be a maximal element of F and suppose that c∨d ∈M. Consider the sets
Mc = {y ∈L : ∃x ∈M y ≥x ∧c},
Md = {y ∈L : ∃x ∈M y ≥x ∧d}.
If b ∈Mc ∩Md, then there are x, y ∈M such that b ≥x ∧c and b ≥y ∧d. It
follows that
b ≥(x ∧c) ∨(y ∧d) = (x ∨y) ∧(x ∨d) ∧(c ∨y) ∧(c ∨d) ∈M,
whence b ∈M contrary to assumption. Therefore b /∈Mc or b /∈Md. In the first
case Fc is then a filter ⊇M and so M = Mc by the maximality of M, whence
c ∈m. Similarly, in the second case, d ∈M. Accordingly M is prime.
This proposition has the following immediate consequences
Corollary 0.4 For any elements a, b of a distributive lattice such that a ≰b
there is a prime filter containing a but not b.
Corollary 0.5 Each filter in a distributive lattice L with top and bottom
elements is included in an ultrafilter.
If L and L′ are distributive lattices, a map h : L →L′ is a lattice homomorph-
ism if it satisfies: h(0) = 0, h(1) = 1, h(x∧y) = h(x)∧h(y), h(x∨y) = h(x)∨h(y)
for arbitrary x, y ∈L. Lattice homomorphisms are clearly order preserving. A
homomorphism h: L →L′ is complete if, for any X ⊆L such that ∨X exists in
L, ∨h[x] exists in L′ and equals h(∨X). If h: L →L′ is a homomorphism, and
L′ nontrivial, the set h−1[1] = {x : h(x) = 1}—the hull of f—is a filter, and
h−1[0] = {x : h(x) = 0}—the kernel of f—an ideal in L. When h : L →2, the
filter h−1[1] is a prime filter. Conversely, each prime filter P in L determines a
homomorphism h : L →2 defined by h(x) = 1 iffx ∈P.
If H and H′ are Heyting algebras, a lattice homomorphism h : H →H′ is
an algebra homomorphism if h(x ⇒y) = h(x) ⇒h(y) for arbitrary x, y ∈H.
When h : H →2, the filter h−1[1] is an ultrafilter. Conversely, each ultrafilter
U in H determines an algebra homomorphism h : H →2 defined by h(x) = 1
iffx ∈U.

```

## PDF page 030 | printed page 10

```text
10
BOOLEAN AND HEYTING ALGEBRAS
It is easily verified that, for Boolean algebras B, B′, a map h : B →B′
is a(n) (algebra) homomorphism iffit satisfies either of the two equivalent
conditions: (i) h(x ∧y) = h(x) ∧h(y), h(x∗) = h(x)∗for all x, y ∈B; (ii)
h(x ∨y) = h(x) ∨h(y), h(x∗) = h(x)∗for all x, y ∈B. Moreover, h is injective iff
h−1[1] = 1, or, equivalently, if h−1[0] = 0.
If I is an ideal in a Boolean algebra B, we define the quotient algebra B/I as
follows. Introduce the relation ∼I on B by a∼Ib iff, for some x ∈I, a∨x = b∨x.
It is easily verified that ∼I is a congruence relation on B, that is, an equivalence
relation satisfying the condition:
If a ∼I a′, b ∼I b′, then a ∨b ∼I a′ ∨b′, a ∧b ∼I a′ ∧b′, a∗∼I a′∗.
Writing a/I for the ∼I-equivalence class of a, it follows that the set B/I =
{a/I : a ∈B} can be assigned the structure of a Boolean algebra by defining
a/I ∧b/I = (a ∧b)/I, a/I ∨b/I = (a ∨b)/I, (a/I)∗= a∗/I. The top and bottom
elements of B/I are 1/I and 0/I. The map h : B →B/I given by h(a) = a/I
is then a homomorphism onto B/I called the canonical homomorphism. Clearly
the kernel of h is I.
Similarly, starting with a filter F in B and defining the congruence relation
≈F on B by a ≈F b iff, for some x ∈F, a ∧x = b ∧x yields the quotient
algebra B/F: in this case the hull of the corresponding canonical homomorphism
B →B/F is F.
A bijective homomorphism is called an isomorphism; two lattices, Heyting,
or Boolean algebras are isomorphic if there exists an isomorphism between them.
If B and B′ are Boolean algebras, a homomorphism h : B →B′ is complete
if, for any X ⊆B such that [PDF-GLYPH-U+0003] X exists in B, [PDF-GLYPH-U+0003]{h(x) : x ∈X} exists in B′ and
equals h([PDF-GLYPH-U+0003] x). An isomorphism of a Boolean algebra B with itself is called an
automorphism; clearly any automorphism is a complete homomorphism. The set
of all automorphisms of B forms a group under function composition: this group
is called the group of automorphisms of B.
In the sequel we shall require a result concerning the existence of special sorts
of ultrafilters in Boolean algebras, the Rasiowa–Sikorski Theorem. Let S be a
family of subsets of a Boolean algebra B, each member X of which has a join
[PDF-GLYPH-U+0003] X. An ultrafilter U in B is said to be S-complete if for all X ∈S we have
[PDF-GLYPH-U+0003] X ∈U →X ∩U ̸= ∅. Equivalently, U is S-complete if whenever X ⊆U and
{x∗: x ∈X} ∈S, then [PDF-GLYPH-U+0002] X ∈U.
Rasiowa–Sikorski Theorem 0.6 If each member of a countable family S of
subsets of a Boolean algebra B has a join, then for each a ̸= 0 in B there is an
S-complete ultrafilter in B containing a.
Proof Enumerate S as {Tn : n ∈ω} and write tn = [PDF-GLYPH-U+0003] Tn. We define by recursion
a sequence b0, b1, . . . of elements of B such that, for each n ∈ω, bn ∈Tn and
a ∧(t∗
0 ∨b0) ∧· · · ∧(t∗
n ∨bn) ̸= 0.

```

## PDF page 031 | printed page 11

```text
REPRESENTATION THEOREMS FOR DISTRIBUTIVE LATTICES
11
Given n ∈ω, suppose that for each m < n, bm has been found so as to satisfy
the specified conditions. If n = 0, let c = a, and if n > 0 let
c = a ∧(t∗
0 ∨b0) ∧· · · ∧(t∗
n−1 ∨bn−1).
Then if n = 0 we have c ̸= 0 by assumption, and if n > 0 we have c ̸= 0 by
inductive hypothesis. Suppose now, for contradiction’s sake, that c ∧(t∗
n ∨b) = 0
for all b ∈Tn. Then 0 = (c∧t∗
n)∨(c∧b), so that c∧t∗
n = 0 and c∧b = 0, whence
c ≤b∗for all b ∈Tn. Hence
c ≤
[PDF-GLYPH-U+0006]
{b∗: b ∈Tn} = (
[PDF-GLYPH-U+0004]
Tn)∗= t∗
n.
So c = c ∧t∗
n = 0 contradicting the inductive hypothesis.
Accordingly bn can be found to satisfy the specified conditions, and so such a
bn can be found for each n ∈ω. Then the set {a}∪{t∗
n∨bn : n ∈ω} has the f.m.p.
and is therefore included in an ultrafilter U in B. U certainly contains a; we show
that U is S-complete. If [PDF-GLYPH-U+0003] Tn = tn ∈U, then, since t∗
n ∨bn ∈U by construction,
it follows that bn = tn ∧bn = tn ∧(t∗
n ∨bn) ∈U, so that Tn ∩U ̸= ∅.
Representation theorems for distributive lattices
We state and prove three representation theorems:
Theorem 0.7 Any distributive lattice is isomorphic to a lattice of sets.
Theorem 0.8 Any Heyting algebra is isomorphic to an algebra of opens.
Theorem 0.9 (The Stone Representation Theorem) Any Boolean algebra
is isomorphic to a field of sets.
The proofs of these theorems all rest on the introduction of the set P(L) of
prime filters in a distributive lattice L. There is a canonical map p : L →P(P(L))
defined by p(x) = {P ∈P(L) : x ∈P} for x ∈L. It is easy to verify that p
is a lattice homomorphism; it follows from corollary 0.4 that p is injective, and
hence an isomorphism of L with the lattice of sets {p(x) : x ∈L}. This proves
Theorem 0.7.
To prove Theorem 0.8 we start with a Heyting algebra H and impose a certain
topology on P(H). As a base for this topology we take the family {p(x) : x ∈H}.
Write X for the resulting topological space. We show that, for x, y ∈H,
(∗)
p(x ⇒y) =
◦








[X −p(x)] ∪p(y) = p(x) ⇒p(y).

```

## PDF page 032 | printed page 12

```text
12
BOOLEAN AND HEYTING ALGEBRAS
To prove (∗) we first observe that
P ∈
◦








[X −p(x)] ∪p(y) ↔∃z[P ∈p(z) ⊆[X −p(x)] ∪p(y)]
(∗∗)
↔∃z ∈P[∀Q ∈X[z ∈Q →[Q /∈p(x) or Q ∈p(y)]]]
↔∃z ∈P[∀Q ∈X[z ∈Q →[x ∈Q →y ∈Q]]]
↔∃z ∈P[∀Q ∈X[z ∈Q and x ∈Q →y ∈Q]].
Next, we note that
(∗∗∗)
z ≤x ⇒y ↔z ∧x ≤y ↔
∀Q ∈X[z ∈Q and x ∈Q →y ∈Q].
For if z ∧x ≤y, and Q ∈X satisfies z ∈Q and x ∈Q, then z ∧x ∈Q, whence
y ∈Q. Conversely, suppose that, for every Q ∈X, z ∈Q and x ∈Q →y ∈Q. If
z ∧x ≰y, then by Corollary 0.4 there is Q ∈X containing z ∧x and hence both
z and x but not y, contradicting assumption. Hence z ∧x ≤y.
It now follows from (∗∗) and (∗∗∗) that
P ∈
◦








[X −p(x)] ∪p(y) ↔∃z ∈P[z ≤x ⇒y] ↔x ⇒y ∈P ↔P ∈p(x ⇒y),
which immediately yields (∗).
Therefore p is an algebra homomorphism of H into O(X). We have already
seen that it is injective, so it is an isomorphism of H with the algebra of opens
{p(x) : x ∈H}. This proves Theorem 0.8.
Finally we prove Theorem 0.9. Let B be a Boolean algebra. We have already
shown that the canonical homomorphism p : B →P(P(B)) is an isomorphism
of B with the lattice of sets ˜B = {p(x) : x ∈L}. It is readily seen that, since B
is a Boolean algebra, p preserves complements, so that ˜B is a field of sets and p
an isomorphism between the Boolean algebras B and ˜B.
Connections with logic
Heyting and Boolean algebras have close connections with intuitionistic and
classical logic,5 respectively.
5For accounts of both systems of logic, see, for example, Bell and Machover 1977.

```

## PDF page 033 | printed page 13

```text
CONNECTIONS WITH LOGIC
13
Intuitionistic first-order logic has the following axioms and rules of inference.
Axioms
ϕ →(ψ →ϕ)
[ϕ →(ψ →χ) →[(ϕ →ψ) →(ϕ →χ)]
ϕ →(ψ →ϕ ∧ψ)
ϕ ∧ψ →ϕ
ϕ ∧ψ →ψ
ϕ →ϕ ∨ψ
ψ →ϕ ∨ψ
[ϕ →(ψ →χ) →[(ϕ →ψ) →(ϕ →χ)]
(ϕ →χ) →[(ψ →χ) →(ϕ ∨ψ →χ)]
(ϕ →ψ) →[(ϕ →¬ψ) →¬ϕ]
¬ϕ →(ϕ →ψ)
ϕ(t) →∃xϕ(x)
∀xϕ(x) →ϕ(y) (x free in ϕ and t free for x in ϕ)
x = x
ϕ(x) ∧x = y →ϕ(y).
Rules of Inference
ϕ, ϕ →ψ
ψ
ψ →ϕ(x)
ψ →∀xϕ(x)
ϕ(x) →ψ
∃xϕ(x) →ψ .
(x not free in ψ)
Classical first-order logic is obtained by adding to the intuitionistic system the
rule of inference
¬¬ϕ
ϕ .
In intuitionistic logic none of the classically valid logical schemes
LEM (law of excluded middle) ϕ ∨¬ϕ
LDN (law of double negation) ¬¬ϕ →ϕ
DEM (de Morgan’s law) ¬(ϕ ∧ψ) →¬ϕ ∨¬ψ
are derivable. However LEM and LDN are intuitionistically equivalent and DEM
is intuitionistically equivalent to the weakened law of excluded middle:
WLEM ¬ϕ ∨¬¬ϕ.

```

## PDF page 034 | printed page 14

```text
14
BOOLEAN AND HEYTING ALGEBRAS
Also the weakened form of LDN for negated statements,
WLDN ¬¬¬ϕ →¬ϕ
is intuitionistically derivable. It follows that any formula intuitionistically
equivalent to a negated formula satisfies the LDN.
Heyting algebras are associated with theories in intuitionistic logic in the
following way. Given a consistent theory T in an intuitionistic propositional or
first-order language L, define the equivalence relation ≈on the set of formulas of
L by ϕ ≈ψ if T ⊢ϕ ↔ψ. For each formula ϕ write [ϕ] for its ≈-equivalence class.
Now define the relation ≤on the set H(T) of ≈-equivalence classes by [ϕ] ≤[ψ]
if and only if T ⊢ϕ →ψ. Then ≤is a partial ordering of H(T) and the partially
ordered set (H(T), ≤) is a Heyting algebra in which [ϕ] ⇒[ψ] = [ϕ →ψ], with
analogous equalities defining the meet and join operations, 0, and 1. H(T) is
called the the Heyting algebra determined by T. It can be shown that Heyting
algebras of the form H(T) are typical in the sense that, for any Heyting algebra L,
there is a propositional intuitionistic theory T such that L is isomorphic to H(T).
Accordingly Heyting algebras may be identified as the algebras of intuitionistic
logic.
Similarly, starting with a consistent theory T in a classical propositional or
first-order language, the associated algebra B(T) is a Boolean algebra known as
the Lindenbaum algebra of T. Again, it can be shown that any Boolean algebra
is isomorphic to B(T) for a suitable classical theory T.
As regards semantics, Heyting algebras and Boolean algebras have cor-
responding relationships with intuitionistic, and classical, propositional logic,
respectively. Thus, suppose given a propositional language L ; let P be its set
of propositional variables. Given a map f: P →H to a Heyting algebra H, we
extend f to a map ϕ [PDF-GLYPH-U+0017]→[PDF-GLYPH-U+0001]ϕ[PDF-GLYPH-U+0002] of the set of formulas of L to H by:
[PDF-GLYPH-U+0001]ϕ ∧ψ[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]ϕ[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]ψ[PDF-GLYPH-U+0002]
[PDF-GLYPH-U+0001]ϕ ∨ψ[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]ϕ[PDF-GLYPH-U+0002] ∨[PDF-GLYPH-U+0001]ψ[PDF-GLYPH-U+0002]
[PDF-GLYPH-U+0001]ϕ ⇒ψ[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]ϕ[PDF-GLYPH-U+0002] ⇒[PDF-GLYPH-U+0001]ψ[PDF-GLYPH-U+0002]
[PDF-GLYPH-U+0001]¬ϕ[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]ϕ[PDF-GLYPH-U+0002]∗.
A formula ϕ is said to be Heyting valid—written ⊢ϕ—if [PDF-GLYPH-U+0001]ϕ[PDF-GLYPH-U+0002] = 1 for any such
map f. It can then be shown that ϕ is Heyting valid iff⊢ϕ in the intuitionistic
propositional calculus, that is, iffϕ is provable from the propositional axioms
listed above.
Similarly, if we define the notion of Boolean validity by restricting the defin-
ition of Heyting validity to maps into Boolean algebras, then it can be shown
that a formula is Boolean valid iffit is provable in the classical propositional
calculus.
Finally, again as regards semantics, complete Heyting and Boolean algebras
are related to intuitionistic, and classical first-order logic, respectively. To be
precise, let L be a first-order language whose sole extralogical symbol is a binary

```

## PDF page 035 | printed page 15

```text
CONNECTIONS WITH LOGIC
15
predicate symbol P. A Heyting algebra–valued L -structure is a quadruple M =
(M, eq, Q, H), where M is a nonempty class, H is a complete Heyting algebra
and eq and Q are maps M × M →M satisfying, for all m, n, m′, n′ ∈M,
eq(m, m) = 1, eq(m, n) = eq(n, m), eq(m, n) ∧eq(n, n′) ≤eq(m, n′),
Q(m, n) ∧eq(m, m′) ≤Q(m′, n), Q(m, n) ∧eq(n, n′) ≤Q(m, n′).
For any formula ϕ of L and any finite sequence x = ⟨x1, . . . , xn⟩of variables
of L containing all the free variables of ϕ, we define for any Heyting-valued
L -structure M a map
[PDF-GLYPH-U+0001]ϕ[PDF-GLYPH-U+0002]Mx : M n →H
recursively as follows:
[PDF-GLYPH-U+0001]xp = xq[PDF-GLYPH-U+0002]Mx = ⟨m1, . . . , mn⟩[PDF-GLYPH-U+0017]→eq(mp, mq),
[PDF-GLYPH-U+0001]Pxpxq[PDF-GLYPH-U+0002]Mx = ⟨m1, . . . , mn⟩[PDF-GLYPH-U+0017]→Q(mp, mq),
[PDF-GLYPH-U+0001]ϕ ∧ψ[PDF-GLYPH-U+0002]Mx = [PDF-GLYPH-U+0001]ϕ[PDF-GLYPH-U+0002]Mx ∧[PDF-GLYPH-U+0001]ψ[PDF-GLYPH-U+0002]Mx, and similar clauses for the other connectives,
[PDF-GLYPH-U+0001]∃yϕ[PDF-GLYPH-U+0002]Mx = ⟨m1, . . . , mn⟩[PDF-GLYPH-U+0017]→
[PDF-GLYPH-U+0004]
m∈M
[PDF-GLYPH-U+0001]ϕ(y/u)[PDF-GLYPH-U+0002]Mux(m, m1, . . . , mn)
[PDF-GLYPH-U+0001]∀yϕ[PDF-GLYPH-U+0002]Mx = ⟨m1, . . . , mn⟩[PDF-GLYPH-U+0017]→
[PDF-GLYPH-U+0006]
m∈M
[PDF-GLYPH-U+0001]ϕ(y/u)[PDF-GLYPH-U+0002]Mux(m, m1, . . . , mn)
Call ϕ M-valid if [PDF-GLYPH-U+0001]ϕ[PDF-GLYPH-U+0002]Mx is identically 1, where x is the sequence of all free
variables of ϕ. Then it can be shown that ϕ is M-valid for all M iffϕ is provable
in intuitionistic first-order logic. This is the algebraic completeness theorem for
intuitionistic first-order logic.
Similarly, if we carry out the same procedure, replacing complete Heyting
algebras with complete Boolean algebras, one can prove the corresponding algeb-
raic completeness theorem for classical first-order logic, namely, a first-order
formula is valid in every Boolean-valued structure iffit is provable in classical
first-order logic.

```

## PDF page 036 | printed page 16

```text
1
BOOLEAN-VALUED MODELS OF SET THEORY:
FIRST STEPS
Basic set theory
Although it assumed that readers of this book will be familiar with the
development of axiomatic set theory up to the consistency of the axiom of choice
and the generalized continuum hypothesis (e.g., see Cohen 1966; Drake 1974; Bell
and Machover 1977; Kunen 1980), we begin with a brief review of the notions
from set theory that we shall need.
The language of set theory is a first-order language L with equality, which also
includes a binary predicate symbol ∈(membership). The individual variables
v0, v1, . . . , x, y, z, . . . of L are understood to range over sets, but we shall also
permit the formation of class terms {x: ϕ(x)} for each formula ϕ(x). The term
{x: ϕ(x)} is understood to denote ‘the class of all (sets) x such that ϕ(x)’; a
term of this form will be called simply a (definable) class. We assume that
classes satisfy Church’s scheme:
∀y[y ∈{x: ϕ(x)} ↔ϕ(y)].
We shall employ the standard set-theoretic abbreviations, in particular the
following:
∃!xϕ(x)
‘there is a unique x such that ϕ(x)’
dom(f)
domain of f
ran(f)
range of f
Px or P(x)
power set of x
F | X
restriction of F to X
F[X]
image of X under F
⟨x, y⟩
ordered pair of x, y
xy
set of all maps of y into x
Fun(f)
‘f is a function’
Ord(x)
‘x is an ordinal’
L(x)
‘x is constructible’
∅= {x: x ̸= x}
the empty set
V = {x: x = x}
the universe of sets
ORD = {x: Ord(x)}
the class of ordinals
L = {x: L(x)}
the constructible universe.

```

## PDF page 037 | printed page 17

```text
BASIC SET THEORY
17
We shall use lower case Greek letters α, β, γ, ξ, η as variables ranging over
ordinals.
For our purposes Zermelo–Fraenkel set theory (ZF) is the theory in L based
on the following axioms (1)–(7):
(1) Extensionality
∀x∀y[∀z(z ∈x ↔z ∈y) →x = y].
(2) Separation
∀u∃v∀x[x ∈v ↔x ∈u ∧ϕ(x)],
where v is not free in the formula ϕ(x).
(3) Replacement
∀u[∀x ∈u ∃y ϕ(x, y) →∃v ∀x ∈u ∃y ∈v ϕ(x, y)],
where v is not free in the formula ϕ(x, y).
(4) Union
∀u ∃v ∀x[x ∈v ↔∃y ∈u(x ∈y)].
(5) Power set
∀u ∃v ∀x[x ∈v ↔∀y ∈x(y ∈u)].
(6) Infinity
∃u[∅∈u ∧∀x ∈u ∃y ∈u(x ∈y)].
(7) Regularity
∀x[∀y ∈xϕ(y) →ϕ(x)] →∀xϕ(x)],
where y is not free in the formula ϕ(x).
Remarks 1 The forms of the axioms of replacement (3) and regularity (7),
which have been chosen so as to allow easy verification in the models we shall
construct, differ from their customary forms, viz.
(3∗)
∀u[∀x ∈u ∃!y ϕ(x, y) →∃v ∀y[y ∈v ↔∃x ∈u ϕ(x, y)]].
and
(7∗)
∀u[u ̸= ∅→∃x ∈u(x ∩u ̸= ∅)].
It is not difficult to show that the replacing of (3) by (3*) and (7) by (7*) yields
a system equivalent in strength.
2 The usual axiom of pairing has been omitted from our presentation of ZF
because it is derivable from the axioms of replacement, power set, and separation.
The axiom of choice (AC) is the sentence
∀u∃f[Fun(f) ∧dom(f) = u ∧∀x ∈u[x ̸= ∅→f(x) ∈x]].

```

## PDF page 038 | printed page 18

```text
18
BOOLEAN-VALUED MODELS OF SET THEORY
Over ZF the axiom of choice is equivalent to Zorn’s lemma, namely, the assertion
that, for any partially ordered set P in which each chain has a supremum
(or merely an upper bound), P has a maximal element.
The theory ZF + AC is written ZFC.
We conceive of ordinals in such a way that each ordinal coincides with the set
of its predecessors. A cardinal is an ordinal not equipollent (bijective) with any
smaller ordinal. Customarily we use the Greek letters κ, λ to denote infinite
cardinals. We assume that the infinite cardinals are enumerated in a sequence
ℵ0, ℵ1, . . . , ℵα, . . . or, when considered as ordinals, ω0, ω1, . . . , ωα, . . .. The next
cardinal after κ is written κ+; thus, if κ = ℵα, then κ+ = ℵα+1. The cardinality
of a set x—that is, the least cardinal equipollent with x—is denoted by |x|. When
κ and λ are cardinals we usually write κλ for |κλ|. (The context will make it
clear whether a given occurrence of κλ is intended to mean the set of maps from
λ to κ or its cardinality.) Recall that |Px| = 2|x| for any set x. The continuum
hypothesis (CH) is the assertion 2ℵ0 = ℵ1; the generalized continuum hypothesis
(GCH) is the assertion that, for all infinite cardinals κ, 2κ = κ+. An infinite
cardinal κ is said to be regular if whenever |I| < κ and {λi: i ∈I} ⊆κ then
[PDF-GLYPH-U+0001]
i∈I λi < κ. Notice that κ+ is always regular. Also, if GCH holds and κ is
regular, then κλ = κ for any cardinal λ < κ.
For any infinite cardinal κ there is a canonical bijection between κ and κ × κ
defined as follows. We well-order κ × κ by placing ⟨ξ, η⟩before ⟨ξ′, η′⟩provided
the ordered triple ⟨max(ξ, η), ξ, η⟩lexicographically precedes ⟨max(ξ′, η′), ξ′, η′⟩.
Then (see theorem 5.1 of Drake 1974) the canonical bijection of κ with κ × κ is
an order isomorphism. If for each ξ < κ we write ⟨βξ, γξ⟩for the element of κ×κ
paired with ξ under the canonical bijection, it is not hard to show that βξ ≤ξ.
The axiom of constructibility is the sentence ∀xL(x), or equivalently V = L.
We recall the celebrated results of G¨odel that, if ZF is consistent, so is
ZF + V = L, and that GCH and AC are both provable in the latter theory.
We shall need some facts about induction and recursion on well-founded rela-
tions. A class R of ordered pairs is said to be well-founded if for each set u the
class {x: xRu} = Ru is a set and each nonempty set u has an element x such
that yRx for no y ∈u. The second condition is equivalent (assuming AC) to the
assertion that for no sequence of sets x0, x1, . . . do we have xn+1 ∈xn for all n.
Given a well-founded relation R, the principle of induction on R is the
assertion,
∀x[∀y(yRx →ϕ(y)) →ϕ(x)] →∀xϕ(x)
for an arbitrary formula ϕ(x). The principle of recursion on R is the assertion
that if F is any class of ordered pairs, which defines a single-valued mapping of
V into V (such a class is called a function on V ), then there is a function G on
V such that
∀u[G(u) = F(⟨u, G|Ru⟩)].

```

## PDF page 039 | printed page 19

```text
BASIC SET THEORY
19
The principles of induction and recursion on well-founded relations are provable
in ZF as schemes.
It follows from the axiom of regularity that the membership relation is
well-founded, so we may define the sets Vα by recursion as follows:
Vα = {x: ∃ξ < α[x ⊆Vξ]}.
The axiom of regularity implies that ∀x∃α(x ∈Vα), so we may define a function
rank(x) by setting
rank(x) = least α such that x ∈Vα+1.
The relation rank(x) < rank(y) is clearly well-founded, so we may deduce the
principle of induction on rank:
∀x[∀y(rank(y) < rank(x) →ϕ(y)) →ϕ(x)] →∀xϕ(x).
Finally, a few remarks on models of set theory. A(n) (L-) structure is a pair
⟨M, E⟩where M is a nonempty set and E ⊆M × M. We shall customarily
identify a given structure with its underlying set M and write ‘M’ for both. If E
is a well-founded relation, the structure M is said to be well-founded. A transitive
∈-structure is a structure of the form ⟨M, ∈|M⟩in which M is a transitive set
(i.e. satisfies x ∈y ∈M →x ∈M) and ∈|M = {⟨x, y⟩∈M × M: x ∈y} is the
∈-relation restricted to M. A transitive ∈-model of ZF or ZFC is a transitive
∈-structure, which is a model of ZF or ZFC. Mostowski’s collapsing lemma is
the assertion, provable in ZF, that if ⟨M, E⟩is a well-founded structure which is
a model of the axiom of extensionality, then there is a unique isomorphism h of
⟨M, E⟩onto a transitive ∈-structure, where h satisfies h(x) = {h(y) : yEx} for
x ∈M. This transitive ∈-structure is called the transitive collapse of ⟨M, E⟩.
If ϕ(v1, . . . , vn) is an L-formula, M an L-structure, and a1, . . . , an ∈M, we
write M |= ϕ[a1, . . . , an] for ‘a1, . . . , an satisfies ϕ in M’. If M is a model of
ZFC and t a closed term of L, we write t(M) for the interpretation of t in M.
This is defined as follows: if t is a set, then t(M) is the unique a ∈M for
which M |= (v1 = t)[a], while if t is a definable class which is not a set we put
t(M) = {a ∈M: M |= ϕ[a]}.
An L-formula is said to be restricted if each of its quantifiers occurs in the
form ∀x ∈y or ∃x ∈y (i.e. ∀x(x ∈y →· · · ) or ∃x(x ∈y ∧· · · )) or if it can
be proved equivalent in ZFC to a formula of this kind. The formula Ord(x)
is restricted. A formula is Σ1 if it is built up from atomic formulas and their
negations using only the logical operations ∧, ∨, ∀x ∈y, ∃x, or if it can be proved
equivalent in ZFC to such a formula. The formula L(x) is Σ1. The importance
of restricted and Σ1-formulas lies in the following facts. Let ϕ(v1, . . . , vn) be
an L-formula, M a transitive ∈-model of ZFC, and a1, . . . , an ∈M. If ϕ is

```

## PDF page 040 | printed page 20

```text
20
BOOLEAN-VALUED MODELS OF SET THEORY
restricted, then
M |= ϕ[a1, . . . , an] ↔ϕ(a1, . . . , an),
while if ϕ is Σ1,
M |= ϕ[a1, . . . , an] →ϕ(a1, . . . , an).
In conclusion, we point out that, unless otherwise indicated, all theorems
lemmas, problems, etc. in this book are to be regarded as being proved in ZFC.
Construction of the model
Suppose that for each set x ∈V we are given a characteristic function for x, that
is, a function cx taking values in the Boolean algebra 2 = {0, 1} such that x ⊆
dom(cx) and, for all y ∈dom(cx), cx(y) = 1 iffy ∈x. It is clear that all informa-
tion about x is carried by cx, so it is natural to identify x with cx. If we perform
this identification for all x ∈V , we see that V may, in a natural sense, be regarded
as a class of two-valued functions. The snag here is that, although the process
turns each x ∈V into a two-valued function, the function fails to be homogeneous
in that its domain does not (in general) consist of two-valued functions.
Let us examine this notion of homogeneity a little more closely. It is clear
that, however we go about defining it, we should require a two-valued function
to be homogeneous iffits domain is a set of homogeneous two-valued functions.
Now this looks very much like a definition by recursion; and indeed the recursion
in question can be explicitly performed as follows. By transfinite recursion on α
we define
V (2)
α
= {x: Fun(x) ∧ran(x) ⊆2 ∧∃ξ < α[dom(x) ⊆V (2)
ξ
]}
(1.1)
(compare the definition of the Vα!), and then put
V (2) = {x: ∃α[x ∈V (2)
α ]}.
(1.2)
V (2) is then the required class of all homogeneous two-valued functions, since it
is easy to see that we have
x ∈V (2) ↔Fun(x) ∧ran(x) ⊆2 ∧dom(x) ⊆V (2).
(1.3)
In future we shall drop the cumbersome term ‘homogeneous two-valued func-
tion’ and call the members of V (2) simply two-valued sets. From (1.3) we see that
a two-valued set is a two-valued function whose domain is a set of two-valued
sets. The class V (2) is called the universe of two-valued sets; we shall see later
on that, as expected, it is in a natural sense isomorphic to the standard universe
V of sets.

```

## PDF page 041 | printed page 21

```text
CONSTRUCTION OF THE MODEL
21
What we now propose to do is to replace the Boolean algebra 2 by an arbitrary
complete Boolean algebra B, thus obtaining what we shall call the universe V (B)
of B-valued sets. We shall show that there is a natural way of assigning to each
sentence σ of the language of set theory an element [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B of B which will act as
the ‘Boolean truth value’ of σ in the universe V (B). Calling the sentence σ true
in V (B) if [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B = 1B, and false in V (B) if [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B = 0B (cf. classical notion of
truth and falsehood), we show that, for any complete Boolean algebra B, all the
theorems of ZFC are true in V (B), or, to put it more suggestively, that V (B) is a
‘Boolean-valued model’ of ZFC. On the other hand, we shall see that, by selecting
B carefully, we can arrange for a variety of set-theoretic assertions, for example,
the continuum hypothesis or the axiom of constructibility, to be false in V (B).
The failure of the continuum hypothesis in V (B) will be achieved by selecting B
in such a way that, in V (B), ω has many (e.g. ℵ2 or ℵω+1) ‘B-valued subsets’
which are not subsets in the two-valued sense. In this way we will establish the
independence of the continuum hypothesis from ZFC.
We now suppose given a complete Boolean algebra B, which we will assume
to be fixed throughout the rest of this chapter. We also assume that B is a set,
that is, B ∈V .
We define the universe V (B) of B-valued sets by analogy with (1.2); namely,
we define, by recursion on α,
V (B)
α
= {x: Fun(x) ∧ran(x) ⊆B ∧∃ξ < α[dom(x) ⊆V (B)
ξ
]}
(1.4)
and
V (B) = {x: ∃α[x ∈V (B)
α
]}.
(1.5)
We see immediately that, as in (1.3), we have
x ∈V (B) ↔Fun(x) ∧ran(x) ⊆B ∧dom(x) ⊆V (B),
(1.6)
that is, a B-valued set is a B-valued function whose domain is a set of
B-valued sets. V (B) is called a Boolean extension of V, or, more precisely, the
B-extension of V.
An easy induction on rank argument proves:
1.7 Induction Principle for V (B). For any formula φ(x),
∀x ∈V (B)[∀y ∈dom(x)φ(y) →φ(x)] →∀x ∈V (B)φ(x).
We now introduce a first-order language suitable for making statements about
V (B). Let L(B) be the first-order language obtained from L by adding a name
for each element of V (B). For convenience we agree to identify each element of
V (B) with its name in L(B). By coding the formulas of L(B) as sets in V in the

```

## PDF page 042 | printed page 22

```text
22
BOOLEAN-VALUED MODELS OF SET THEORY
usual way, it is clear that the collection of formulas of L(B) becomes a definable
class.
At this point it will be convenient to introduce the following terminological
convention, which will be adhered to throughout the rest of the book. By for-
mula, or sentence we shall mean L-formula, or L-sentence, respectively, and
by B-formula, or B-sentence we shall mean L(B)-formula, or L(B)-sentence,
respectively.
We next set about constructing the map [PDF-GLYPH-U+0001]·[PDF-GLYPH-U+0002]B from the class of all B-sentences
to B, which assigns to each B-sentence σ the Boolean truth value of σ in V (B).
Suppose for the sake of argument that Boolean truth values have been
assigned to all atomic B-sentences, that is, sentences of the form u = v, u ∈v,
for u, v ∈V (B). Then it is natural—by analogy with the classical two-valued
case—to extend the assignment of Boolean truth values to all B-sentences
inductively as follows. For B-sentences σ, τ we put
[PDF-GLYPH-U+0001]σ ∧τ[PDF-GLYPH-U+0002]B =df [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B ∧[PDF-GLYPH-U+0001]τ[PDF-GLYPH-U+0002]B;
(1.8)
[PDF-GLYPH-U+0001]¬σ[PDF-GLYPH-U+0002]B =df ([PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B)∗.
(1.9)
If φ(x) is a B-formula with one free variable x, such that [PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002]B has been
defined for all u ∈V (B), we observe that the definable class {[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002]B: u ∈V (B)}
is a subset of B and define
[PDF-GLYPH-U+0001]∃xφ(x)[PDF-GLYPH-U+0002]B =df
[PDF-GLYPH-U+0004]
u∈V (B)
[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002]B.
(1.10)
From (1.8)–(1.10) it follows immediately that
[PDF-GLYPH-U+0001]σ ∨τ[PDF-GLYPH-U+0002]B = [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B ∨[PDF-GLYPH-U+0001]τ[PDF-GLYPH-U+0002]B;
(1.11)
[PDF-GLYPH-U+0001]σ →τ[PDF-GLYPH-U+0002]B = [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B ⇒[PDF-GLYPH-U+0001]τ[PDF-GLYPH-U+0002]B;
(1.12)
[PDF-GLYPH-U+0001]σ ↔τ[PDF-GLYPH-U+0002]B = [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B ⇔[PDF-GLYPH-U+0001]τ[PDF-GLYPH-U+0002]B;
(1.13)
[PDF-GLYPH-U+0001]∀xφ(x)[PDF-GLYPH-U+0002]B =
[PDF-GLYPH-U+0006]
u∈V (B)
[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002]B.
(1.14)
It remains to assign Boolean truth values to the atomic B-sentences. Now we
certainly want the axiom of extensionality to hold in V (B), so we should have
[PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002]B = [PDF-GLYPH-U+0001]∀x ∈u[x ∈v] ∧∀y ∈v[y ∈u][PDF-GLYPH-U+0002]B.
Also, in accordance with the logical truth u ∈v ↔∃y ∈v[u = y], which we
certainly want to be true in V (B), it should be the case that
[PDF-GLYPH-U+0001]u ∈v[PDF-GLYPH-U+0002]B = [PDF-GLYPH-U+0001]∃y ∈v[u = y][PDF-GLYPH-U+0002]B.

```

## PDF page 043 | printed page 23

```text
CONSTRUCTION OF THE MODEL
23
Finally, we shall require that the Boolean truth value of restricted formulas like
∃x ∈uφ(x) and ∀x ∈uφ(x) depend only on the Boolean truth values of φ(x) for
those x which are actually in dom(u). Moreover, in evaluating the Boolean truth
value of such formulas, we agree to be guided by our original case of characteristic
functions, where, for x ∈dom(u), the ‘truth value’ of the formula x ∈u is u(x).
Granded all this, it seems reasonable to require that
[PDF-GLYPH-U+0001]∃x ∈uφ(x)[PDF-GLYPH-U+0002]B =
[PDF-GLYPH-U+0004]
x∈dom(u)
[u(x) ∧[PDF-GLYPH-U+0001]φ(x)[PDF-GLYPH-U+0002]B]
and
[PDF-GLYPH-U+0001]∀x ∈uφ(x)[PDF-GLYPH-U+0002]B =
[PDF-GLYPH-U+0006]
x∈dom(u)
[u(x) ⇒[PDF-GLYPH-U+0001]φ(x)[PDF-GLYPH-U+0002]B].
Putting these things together, we see that we must have, for u, v ∈V (B),
[PDF-GLYPH-U+0001]u ∈v[PDF-GLYPH-U+0002]B =
[PDF-GLYPH-U+0004]
y∈dom(v)
[v(y) ∧[PDF-GLYPH-U+0001]u = y[PDF-GLYPH-U+0002]B];
(1.15)
[PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002]B =
[PDF-GLYPH-U+0006]
x∈dom(u)
[u(x) ⇒[PDF-GLYPH-U+0001]x ∈v[PDF-GLYPH-U+0002]B]
∧
[PDF-GLYPH-U+0006]
y∈dom(v)
[v(y) ⇒[PDF-GLYPH-U+0001]y ∈u[PDF-GLYPH-U+0002]B].
(1.16)
Now (1.15) and (1.16) may (and shall) be regarded as a definition of [PDF-GLYPH-U+0001]u ∈v[PDF-GLYPH-U+0002]B
and [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002]B by recursion on a certain well-founded relation. To see this, define
for x, y, u, v ∈V B,
⟨x, y⟩< ⟨u, v⟩iffeither (x ∈dom(u) and y = v) or (x = u and y ∈dom(v)).
Then < is easily seen to be a well-founded relation on the class V (B)×V (B) =
{⟨x, y⟩: x ∈V (B) ∧y ∈V (B)}. If we now put, for u, v ∈V (B),
G(⟨u, v⟩) = ⟨[PDF-GLYPH-U+0001]u ∈v[PDF-GLYPH-U+0002]B, [PDF-GLYPH-U+0001]v ∈u[PDF-GLYPH-U+0002]B, [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002]B, [PDF-GLYPH-U+0001]v = u[PDF-GLYPH-U+0002]B⟩,
then (1.15) and (1.16) may be written, for some class function F,
G(⟨u, v⟩) = F(⟨u, v, G|{⟨x, y⟩: ⟨x, y⟩< ⟨u, v⟩}⟩).
This constitutes a definition of G by recursion on <, and from G we obtain
[PDF-GLYPH-U+0001]u ∈v[PDF-GLYPH-U+0002]B, [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002]B.
Accordingly, we take (1.15) and (1.16) as a definition of [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B for atomic
B-sentences σ, and then define [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B for all B-sentences σ by induction on the
complexity of σ in accordance with (1.8)–(1.10).

```

## PDF page 044 | printed page 24

```text
24
BOOLEAN-VALUED MODELS OF SET THEORY
Remarks 1 The construction of [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B for arbitrary σ evidently has the form of a
truth definition for set theory and so cannot be completely formalized within the
language of set theory. In fact, although the reader will quickly convince himself
that for each specific sentence σ of the language of set theory a specific value for
[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B can be written down within that language, the machinery available in ZFC
is not (unless ZFC is inconsistent) strong enough to formalize the construction of
the map σ [PDF-GLYPH-U+0017]→[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B as a function of σ. More precisely, one can prove in ZFC that
the collection of all pairs ⟨σ, [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B⟩is not a definable class. We must therefore
think of this map as being defined metalinguistically. This tiresome point can be
circumvented by starting with a specific model M of ZFC such that M ∈V and
performing the whole construction of V (B), [PDF-GLYPH-U+0001]·[PDF-GLYPH-U+0002]B within M; cf. Chapter 4.
2 We observe that there is a considerable duplication of elements in V (B). For
example, if for each α ∈ORD we define Zα ∈V (B) by Zα = {⟨x, 0B⟩: x ∈V (B)
α
},
it is easy to verify that [PDF-GLYPH-U+0001]Zα = ∅[PDF-GLYPH-U+0002]B = 1 for all α, so that each of the different
members of the proper class {Zα: α ∈ORD} ‘represents’ the empty set in V (B).
In fact it is not hard to show that, for each u ∈V (B) there is a proper class
of v ∈V (B) such that [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002]B = 1. Accordingly it is helpful to think of the
members of V (B) as ‘representatives’ or ‘labels’ for sets1 (or even ‘potential’
sets), on which (Boolean-valued) equality is defined as an equivalence relation
with very large equivalence classes. The duplication of elements in V (B) could be
avoided by agreeing to identify all elements u, v ∈V (B) such that [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002]B = 1,
but there would be no particular gain for our purposes.
We say that a B-sentence σ is true or holds with probability 1 in V (B), and
frequently write
V (B) |= σ,
if [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B = 1. A B-formula is true in V (B) if its universal closure is true in V (B).
Finally, a rule of inference is valid in V (B) if it preserves the truth of formulas
in V (B).
From now on we shall usually (although not always) take the liberty of
dropping the sub- or super-script from [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B, 0B, 1B.
Our next result is basic.
Theorem 1.17 All the axioms of the first-order predicate calculus with equality
are true in V (B), and all its rules of inference are valid in V (B). In particular,
we have
(i) [PDF-GLYPH-U+0001]u = u[PDF-GLYPH-U+0002] = 1;
(ii) u(x) ≤[PDF-GLYPH-U+0001]x ∈u[PDF-GLYPH-U+0002] for x ∈dom(u);
(iii) [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]v = u[PDF-GLYPH-U+0002];
(iv) [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]v = w[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]u = w[PDF-GLYPH-U+0002];
1V (B) may also be thought of as a ‘label space’ in the terminology of Cohen (1966).

```

## PDF page 045 | printed page 25

```text
CONSTRUCTION OF THE MODEL
25
(v) [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]u ∈w[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]v ∈w[PDF-GLYPH-U+0002];
(vi) [PDF-GLYPH-U+0001]v = w[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]u ∈v[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]u ∈w[PDF-GLYPH-U+0002];
(vii) [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]φ(v)[PDF-GLYPH-U+0002].
for any B-formula φ(x).
Proof We sketch proofs of (i)–(vii), leaving the rest to the reader.
(i) We employ the induction principle for V (B).
Assume as inductive
hypothesis that [PDF-GLYPH-U+0001]x = x[PDF-GLYPH-U+0002] = 1 for x ∈dom(u). Them for x ∈dom(u) we have
(∗)
[PDF-GLYPH-U+0001]x ∈u[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
y∈dom(u)
u(y) ∧[PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002] ≥u(x) ∧[PDF-GLYPH-U+0001]x = x[PDF-GLYPH-U+0002] = u(x).
Therefore [PDF-GLYPH-U+0001]u = u[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0002]
x∈dom(u)[u(x) ⇒[PDF-GLYPH-U+0001]x ∈u[PDF-GLYPH-U+0002]] = 1, and the result follows.
(ii) is proved as in (∗) above, using (i).
(iii) holds by symmetry.
(iv) is proved using the induction principle for V (B). Assume as inductive
hypothesis that
∀v, w ∈V (B)[[PDF-GLYPH-U+0001]x = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]v = w[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]x = w[PDF-GLYPH-U+0002]]
for x ∈dom(u). It follows that, for x ∈dom(u), y ∈dom(v), z ∈dom(w), we
have
[PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]y = z[PDF-GLYPH-U+0002] ∧w(z) ≤[PDF-GLYPH-U+0001]x = z[PDF-GLYPH-U+0002] ∧w(z).
Taking the supremum over z we get, using the definition of [PDF-GLYPH-U+0001]· ∈·[PDF-GLYPH-U+0002],
[PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]y ∈w[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]x ∈w[PDF-GLYPH-U+0002].
But from the definition of [PDF-GLYPH-U+0001]· = ·[PDF-GLYPH-U+0002] we have
[PDF-GLYPH-U+0001]v = w[PDF-GLYPH-U+0002] ∧v(y) ≤[PDF-GLYPH-U+0001]y ∈w[PDF-GLYPH-U+0002]
and also
[PDF-GLYPH-U+0001]v = w[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002] ∧v(y) ≤[PDF-GLYPH-U+0001]x ∈w[PDF-GLYPH-U+0002].
Now take the supremum over y to get
[PDF-GLYPH-U+0001]x ∈v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]v = w[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]x ∈w[PDF-GLYPH-U+0002].

```

## PDF page 046 | printed page 26

```text
26
BOOLEAN-VALUED MODELS OF SET THEORY
Since
[PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] ∧u(x) ≤[PDF-GLYPH-U+0001]x ∈v[PDF-GLYPH-U+0002],
it follows that
[PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]v = w[PDF-GLYPH-U+0002] ∧u(x) ≤[PDF-GLYPH-U+0001]x ∈w[PDF-GLYPH-U+0002]
or
[PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]v = w[PDF-GLYPH-U+0002] ≤[u(x) ⇒[PDF-GLYPH-U+0001]x ∈w[PDF-GLYPH-U+0002]].
Hence
[PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]v = w[PDF-GLYPH-U+0002] ≤
[PDF-GLYPH-U+0006]
x∈dom(u)
[u(x) ⇒[PDF-GLYPH-U+0001]x ∈w[PDF-GLYPH-U+0002]],
(1)
Now, using (iii), the inductive hypothesis implies
∀u, w ∈V (B)[[PDF-GLYPH-U+0001]w = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]v = x[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]w = x[PDF-GLYPH-U+0002]],
and, using this, an argument similar to that for (1) yields
[PDF-GLYPH-U+0001]w = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]v = u[PDF-GLYPH-U+0002] ≤
[PDF-GLYPH-U+0006]
x∈dom(w)
[w(z) ⇒[PDF-GLYPH-U+0001]z ∈u[PDF-GLYPH-U+0002]].
(2)
Putting (1) and (2) together gives (iv).
(v) If z ∈dom(w), then (iv) gives
[PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]u = z[PDF-GLYPH-U+0002] ∧w(z) ≤[PDF-GLYPH-U+0001]v = z[PDF-GLYPH-U+0002] ∧w(z).
Taking the supremum over z, we get (v).
(vi) If y ∈dom(v), then by definition of [PDF-GLYPH-U+0001]v = w[PDF-GLYPH-U+0002] we have
[PDF-GLYPH-U+0001]v = w[PDF-GLYPH-U+0002] ∧v(y) ≤[PDF-GLYPH-U+0001]y ∈w[PDF-GLYPH-U+0002]
and so, using (v), we get
[PDF-GLYPH-U+0001]v = w[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]u = y[PDF-GLYPH-U+0002] ∧v(y) ≤[PDF-GLYPH-U+0001]u ∈w[PDF-GLYPH-U+0002].
Taking the supremum over y gives (vi).
Finally, (vii) is proved by a straightforward induction on the complexity of
φ, something we leave to the reader.

```

## PDF page 047 | printed page 27

```text
CONSTRUCTION OF THE MODEL
27
Remark
By analogy with the case of characteristic functions, one might expect
equality to hold in Theorem 1.17(ii). Although it is easy to show that this is not
the case in general (a task we entrust to the reader), it is nonetheless ‘almost’
the case. In fact, let us call an element v ∈V (B) extensional if v(x) = [PDF-GLYPH-U+0001]x ∈v[PDF-GLYPH-U+0002]
whenever x ∈dom(v). Then for each u ∈V (B) there is an extensional v ∈V (B)
such that [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] = 1. (Simply put v = {⟨x, [PDF-GLYPH-U+0001]x ∈u[PDF-GLYPH-U+0002]⟩: x ∈dom(u)}.)
It follows from Theorem 1.17 that all the theorems of first-order predicate
calculus are true in V (B).
We can now prove the laws governing the assignment of Boolean truth values
to formulas with restricted quantifiers.
Corollary 1.18 For any B-formula φ(x) with one free variable x, and all
u ∈V (B),
(i) [PDF-GLYPH-U+0001]∃x ∈uφ(x)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0003]
x∈dom(u)
[u(x) ∧[PDF-GLYPH-U+0001]φ(x)[PDF-GLYPH-U+0002]];
(ii) [PDF-GLYPH-U+0001]∀x ∈uφ(x)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0002]
x∈dom(u)
[u(x) ⇒[PDF-GLYPH-U+0001]φ(x)[PDF-GLYPH-U+0002]].
Proof We need only establish (i); (ii) then follows by duality. We have
[PDF-GLYPH-U+0001]∃x ∈uφ(x)[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]∃x[x ∈u ∧φ(x)][PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0004]
y∈V (B)
[PDF-GLYPH-U+0001]y ∈u ∧φ(y)[PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0004]
y∈V (B)
[PDF-GLYPH-U+0004]
x∈dom(u)
[[PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002] ∧u(x) ∧[PDF-GLYPH-U+0001]φ(y)[PDF-GLYPH-U+0002]]
=
[PDF-GLYPH-U+0004]
x∈dom(u)
[u(x) ∧
[PDF-GLYPH-U+0004]
y∈V (B)
[PDF-GLYPH-U+0001]x = y ∧φ(y)[PDF-GLYPH-U+0002]]
=
[PDF-GLYPH-U+0004]
x∈dom(u)
[u(x) ∧[PDF-GLYPH-U+0001]∃y[x = y ∧φ(y)][PDF-GLYPH-U+0002]]
=
[PDF-GLYPH-U+0004]
x∈dom(u)
[u(x) ∧[PDF-GLYPH-U+0001]φ(x)[PDF-GLYPH-U+0002]].
Our next result shows precisely how the properties of V (B) can be used
to produce relative consistency proofs in set theory. Given a theory T, write
Consis(T) for ‘T is consistent’. Then we have
Theorem
1.19 Let T, T ′ be extensions of ZF such that Consis(ZF)
→
Consis(T ′), and suppose that in L we can define a constant term B such that:
(∗)
T ′ ⊢B is a complete Boolean algebra and, for each axiom τ of T, we
have T ′ ⊢[PDF-GLYPH-U+0001]τ[PDF-GLYPH-U+0002]B = 1B.
Then Consis(ZF) →Consis(T).

```

## PDF page 048 | printed page 28

```text
28
BOOLEAN-VALUED MODELS OF SET THEORY
Proof If T is inconsistent, then for some axioms τ1, . . . , τn of T we would have,
for any sentence σ,
⊢τ1 ∧· · · ∧τn →σ ∧¬σ.
(1)
Now let B be a complete Boolean algebra satisfying (∗). Then
T ′ ⊢[PDF-GLYPH-U+0001]τ1 ∧· · · ∧τn[PDF-GLYPH-U+0002]B = 1B.
(2)
But (1) gives
T ′ ⊢[PDF-GLYPH-U+0001]τ1 ∧· · · ∧τn[PDF-GLYPH-U+0002]B ≤[PDF-GLYPH-U+0001]σ ∧¬σ[PDF-GLYPH-U+0002]B = 0B,
so that, by (2)
T ′ ⊢1B ≤0B,
so T ′, and hence ZF, would be inconsistent.
Using the standard techniques of arithmetization, Theorem 1.19 can be stated
as follows: if T, T ′ are extensions of ZF such that (∗) holds and Consis(ZF) →
Consis(T ′) is provable in first-order arithmetic, then Consis(ZF) →Consis(T)
is also provable in first-order artithmetic. Accordingly, Theorem 1.19 shows that
method of Boolean-valued models can furnish purely finitary relative consistency
proofs.
Remark V (B) may be regarded as a Boolean-valued structure. (cf. Ch. 0) Given
a complete Boolean algebra B, we here consider a B-valued structure to be a
triple S consisting of a class S and two maps
[PDF-GLYPH-U+0001]· = ·[PDF-GLYPH-U+0002]S, [PDF-GLYPH-U+0001]· ∈·[PDF-GLYPH-U+0002]S : S × S →B
satisfying the analogues of (i), (iii)–(vi) of Theorem 1.17, that is,
[PDF-GLYPH-U+0001]s = s[PDF-GLYPH-U+0002]S = 1,
[PDF-GLYPH-U+0001]s = t[PDF-GLYPH-U+0002]S = [PDF-GLYPH-U+0001]t = s[PDF-GLYPH-U+0002]S,
[PDF-GLYPH-U+0001]s = t[PDF-GLYPH-U+0002]S ∧[PDF-GLYPH-U+0001]t = u[PDF-GLYPH-U+0002]S ≤[PDF-GLYPH-U+0001]s = u[PDF-GLYPH-U+0002]S,
[PDF-GLYPH-U+0001]s = t[PDF-GLYPH-U+0002]S ∧[PDF-GLYPH-U+0001]s ∈u[PDF-GLYPH-U+0002]S ≤[PDF-GLYPH-U+0001]t ∈u[PDF-GLYPH-U+0002]S,
[PDF-GLYPH-U+0001]t = u[PDF-GLYPH-U+0002]S ∧[PDF-GLYPH-U+0001]s ∈t[PDF-GLYPH-U+0002]S ≤[PDF-GLYPH-U+0001]s ∈u[PDF-GLYPH-U+0002]S,
for all s, t, u ∈S.

```

## PDF page 049 | printed page 29

```text
SUBALGEBRAS AND THEIR MODELS
29
The assignment of Boolean values can then be extended recursively to
sentences of the language L augmented by names for all elements of S as in
(1.8)–(1.10), that is,
[PDF-GLYPH-U+0001]σ ∧τ[PDF-GLYPH-U+0002]S = [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]S ∧[PDF-GLYPH-U+0001]τ[PDF-GLYPH-U+0002]S,
[PDF-GLYPH-U+0001]¬σ[PDF-GLYPH-U+0002]S = [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]∗
S
[PDF-GLYPH-U+0001]∃xφ(x)[PDF-GLYPH-U+0002]S =
[PDF-GLYPH-U+0004]
s∈S
[PDF-GLYPH-U+0001]φ(s)[PDF-GLYPH-U+0002]S,
One then show easily by induction on complexity of sentences that the analogue
of Theorem 1.17(vii) holds for S, that is, for any L-formula φ(x) and s, t ∈S,
[PDF-GLYPH-U+0001]s = t[PDF-GLYPH-U+0002]S ∧[PDF-GLYPH-U+0001]φ(s)[PDF-GLYPH-U+0002]S ≤[PDF-GLYPH-U+0001]φ(t)[PDF-GLYPH-U+0002]S.
Subalgebras and their models
A complete Boolean algebra B′ is said to be a complete subalgebra of B if B′ is
a subalgebra of B and, for any X ⊆B′, [PDF-GLYPH-U+0003] X and [PDF-GLYPH-U+0002] X formed in B′ are the same
as [PDF-GLYPH-U+0003] X and [PDF-GLYPH-U+0002] X, respectively, formed in B. Our next result shows that, if B′ is a
complete subalgebra of B, then V (B′) is, in a natural sense, a submodel of V (B).
Theorem 1.20 Let B′ be a complete subalgebra of B. Then
(i) V (B′) ⊆V (B).
Moreover, for u, v ∈V (B′),
(ii) [PDF-GLYPH-U+0001]u ∈v[PDF-GLYPH-U+0002]B′ = [PDF-GLYPH-U+0001]u ∈v[PDF-GLYPH-U+0002]B;
(iii) [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002]B′ = [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002]B.
Proof (i) is clear, while (ii) and (iii) are proved simultaneously by induction on
the well-founded relation y ∈dom(x). Details are left to the reader. (Hint: the
inductive hypothesis is: for all y ∈dom(v) and all u ∈V (B),
[PDF-GLYPH-U+0001]u ∈y[PDF-GLYPH-U+0002]B′ = [PDF-GLYPH-U+0001]u ∈y[PDF-GLYPH-U+0002]B
[PDF-GLYPH-U+0001]u = y[PDF-GLYPH-U+0002]B′ = [PDF-GLYPH-U+0001]u = y[PDF-GLYPH-U+0002]B
[PDF-GLYPH-U+0001]y ∈u[PDF-GLYPH-U+0002]B′ = [PDF-GLYPH-U+0001]y ∈u[PDF-GLYPH-U+0002]B.)
Corollary 1.21 If B′ is a complete subalgebra of B, then, for any restricted
formula φ(v1, . . . , vn) and any u1, . . . , un ∈V (B′),
[PDF-GLYPH-U+0001]φ(u1, . . . , un)[PDF-GLYPH-U+0002]B′ = [PDF-GLYPH-U+0001]φ(u1, . . . , un)[PDF-GLYPH-U+0002]B.

```

## PDF page 050 | printed page 30

```text
30
BOOLEAN-VALUED MODELS OF SET THEORY
Proof By induction on the complexity of φ. For atomic φ the result holds by
Theorem 1.20. The only nontrivial induction step arises when φ is ∃x ∈uψ. And
here we argue as follows: if u, u1, . . . , un ∈V (B), then, writing [PDF-GLYPH-U+0003]B, [PDF-GLYPH-U+0003]B′
for joins
in B, B′ respectively,
[PDF-GLYPH-U+0001]φ(u, u1, . . . , un)[PDF-GLYPH-U+0002]B′ =
[PDF-GLYPH-U+0004]B′
x∈dom(u)
[u(x) ∧[PDF-GLYPH-U+0001]ψ(x, u1, . . . , un)[PDF-GLYPH-U+0002]B′]
=
[PDF-GLYPH-U+0004]B
x∈dom(u)
[u(x) ∧[PDF-GLYPH-U+0001]ψ(x, u1, . . . , un)[PDF-GLYPH-U+0002]B]
= [PDF-GLYPH-U+0001]φ(u, u1, . . . , un)[PDF-GLYPH-U+0002]B.
In this connection we notice that the two-element algebra 2 = {0, 1} is a
complete subalgebra of every complete Boolean algebra B, so that V (2) is a
submodel of every V (B). We are now going to show that V (2) is, in a certain
sense, isomorphic to the standard universe V . To this end we make the following
definition.
Definition 1.22 For each x ∈V ,
ˆx = {⟨ˆy, 1⟩: y ∈x}.
This is a definition by recursion on the well-founded relation y ∈x. Clearly, for
each x ∈V, ˆx ∈V (2) ⊆V (B). Also, by Theorem 1.20, for x, y ∈V we have
[PDF-GLYPH-U+0001]ˆx ∈ˆy[PDF-GLYPH-U+0002]B = [PDF-GLYPH-U+0001]ˆx ∈ˆy[PDF-GLYPH-U+0002]2 ∈2
[PDF-GLYPH-U+0001]ˆx = ˆy[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]ˆx = ˆy[PDF-GLYPH-U+0002]2 ∈2.
We may regard ˆx as being the natural ‘representative’ in V (B) of each x ∈V ,
and accordingly members of V (B) of the form ˆx are called standard. Our next
result establishes the main facts about the standard members of V (B).
Theorem 1.23
(i) For x ∈V, u ∈V (B),
[PDF-GLYPH-U+0001]u ∈ˆx[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
y∈x
[PDF-GLYPH-U+0001]u = ˆy[PDF-GLYPH-U+0002].

```

## PDF page 051 | printed page 31

```text
SUBALGEBRAS AND THEIR MODELS
31
(ii) For x, y ∈V ,
x ∈y ↔V (B) |= ˆx ∈ˆy;
x = y ↔V (B) |= ˆx = ˆy.
(iii) The map x [PDF-GLYPH-U+0017]→ˆx is one–one from V into V (2).
(iv) For each u ∈V (2) there is a unique x ∈V such that V (B) |= u = ˆx.
(v) For any formula φ(v1, . . . , vn) and any x1, . . . , xn ∈V ,
φ(x1, . . . , xn) ↔V (2) |= φ(ˆx1, . . . , ˆxn)
and if φ is restricted then
φ(x1, . . . xn) ↔V (B) |= φ(ˆx1, . . . , ˆxn).
Proof (i) We have
[PDF-GLYPH-U+0001]u ∈ˆx[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
v∈dom(ˆx)
[ˆx(v) ∧[PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002]]
=
[PDF-GLYPH-U+0004]
y∈x
[ˆx(ˆy) ∧[PDF-GLYPH-U+0001]u = ˆy[PDF-GLYPH-U+0002]]
=
[PDF-GLYPH-U+0004]
y∈x
[PDF-GLYPH-U+0001]u = ˆy[PDF-GLYPH-U+0002].
(ii) is established by induction on rank(y), the induction hypothesis being:
for all z with rank(z) < rank (y)
∀x[x ∈z ↔[PDF-GLYPH-U+0001]ˆx ∈ˆz[PDF-GLYPH-U+0002] = 1]
∀x[x = z ↔[PDF-GLYPH-U+0001]ˆx = ˆz[PDF-GLYPH-U+0002] = 1]
∀x[z ∈x ↔[PDF-GLYPH-U+0001]ˆz ∈ˆx[PDF-GLYPH-U+0002] = 1].
We leave the tedious but straightforward details to the reader.
(iii) follows immediately from (ii).
(iv) The uniqueness of x follows from (ii). The existence of x is proved
by induction on the well-founded relation x ∈dom(u). Suppose then that
u ∈V (2) and
∀x ∈dom(u)∃y ∈V [ [PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] = 1].

```

## PDF page 052 | printed page 32

```text
32
BOOLEAN-VALUED MODELS OF SET THEORY
We want to show that, for some v ∈V, [PDF-GLYPH-U+0001]u = ˆv[PDF-GLYPH-U+0002] = 1. Now
[PDF-GLYPH-U+0001]u = ˆv[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0006]
x∈dom(u)
[PDF-GLYPH-U+000F]
u(x) =⇒[PDF-GLYPH-U+0001]x ∈ˆv[PDF-GLYPH-U+0002]
[PDF-GLYPH-U+0010]
∧
[PDF-GLYPH-U+0006]
y∈v
[PDF-GLYPH-U+0001]ˆy ∈u[PDF-GLYPH-U+0002].
So for [PDF-GLYPH-U+0001]u = ˆv[PDF-GLYPH-U+0002] = 1 it is necessary and sufficient that
x ∈dom(u) →u(x) ≤[PDF-GLYPH-U+0001]x ∈ˆv[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
y∈v
[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002];
(1)
y ∈v →1 = [PDF-GLYPH-U+0001]ˆy ∈u[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
x∈dom(u)
[u(x) ∧[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002]].
(2)
Clearly, in order to satisfy (2) we must take
v = {y ∈V : ∃x ∈dom(u)[u(x) = 1 ∧[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] = 1]}.
It follows from (ii) and Replacement that v ∈V , and an application of the
inductive hypothesis shows that v satisfies (1). This proves (iv).
The first part of (v) is proved by induction on the complexity of φ, using (ii)
and (iv). If φ is atomic the result holds by (ii). The only nontrivial induction
step arises when φ in ∃xψ, and this is handled as follows.
Suppose that x1, . . . , xn ∈V . If
[PDF-GLYPH-U+0001]φ(ˆx1, . . . , ˆxn)[PDF-GLYPH-U+0002]2 = 1,
then
[PDF-GLYPH-U+0004]
x∈V (2)
[PDF-GLYPH-U+0001]ψ(x, ˆx1, . . . , ˆxn)[PDF-GLYPH-U+0002]2 = 1
so that
[PDF-GLYPH-U+0001]ψ(x, ˆx1, . . . , ˆxn)[PDF-GLYPH-U+0002]2 = 1
for some x ∈V (2). But, by (iv), for some y ∈V we have [PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002]2 = 1, so that
1 = [PDF-GLYPH-U+0001]ψ(x, ˆx1, . . . , ˆxn)[PDF-GLYPH-U+0002]2 ∧[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002]2
≤[PDF-GLYPH-U+0001]ψ(ˆy, ˆx1, . . . , ˆxn)[PDF-GLYPH-U+0002]2.
The inductive hypothesis now gives ψ(y, x1, . . . , xn), which in turn implies
φ(x1, . . . , xn). The converse is similar.
Finally, the second part of (v) follows from the first part and Corollary 1.21.

```

## PDF page 053 | printed page 33

```text
MIXTURES AND THE MAXIMUM PRINCIPLE
33
Parts (iii), (iv), and (v) of the above theorem show that the universe V (2)
of two-valued sets is, as expected, isomorphic to the standard universe V . In
particular, it follows from (v) that V and V (2) have the same true sentences.
Problem 1.24 (Σ1-formulas in V (B)). Let φ(v1, . . . , vn) be a Σ1-formula, and
let x1, . . . , xn ∈V . Show that
φ(x1, . . . , xn) →V (B) |= φ(ˆx1, . . . , ˆxn).
Mixtures and the Maximum Principle
We are now going to formulate a useful general method for constructing elements
of V (B).
Given a subset {a1 : i ∈I} ⊆B, and a subset {ui : i ∈I} ⊆V (B), we define
the mixture [PDF-GLYPH-U+0001]
i∈I ai · ui of {ui : i ∈I} with respect to {ai : i ∈I} to be that
element u ∈V (B) such that
dom(u) =
[PDF-GLYPH-U+0005]
i∈I
dom(ui)
and, for z ∈dom(u),
u(z) =
[PDF-GLYPH-U+0004]
i∈I
[ai ∧[PDF-GLYPH-U+0001]z ∈ui[PDF-GLYPH-U+0002]].
If I = {0, 1} we write a0 · u0 + a1 · u1 for [PDF-GLYPH-U+0001]
i∈I ai · ui: this is called a two-term
mixture.
A subset A ⊆B is called an antichain in B if a ∧b = 0 for any distinct
elements a, b for A. If an antichain A is given as an indexed set {ai : i ∈I} we
shall always assume that ai ∧aj = 0 whenever i ̸= j in I. A partition of unity in
B is an antichain A in B such that [PDF-GLYPH-U+0003] A = 1.
Our next result justifies the use of the term ‘mixture’ by showing that
under certain mild conditions (in particular, when {ai : i ∈I} is an antichain)
[PDF-GLYPH-U+0001]
i∈I ai · ui behaves as if it were obtained by ‘mixing’ the B-valued sets {ui : i ∈I}
together in (at least) the ‘proportions’ {ai : i ∈I}.
Mixing Lemma 1.25 Let {ai : i ∈I} ⊆B, let {ui : i ∈I} ⊆V (B) and put
[PDF-GLYPH-U+0001]
i∈I ai · ui = u. Suppose that, for all i, j ∈I,
(∗)
ai ∧aj ≤[PDF-GLYPH-U+0001]ui = uj[PDF-GLYPH-U+0002].
Then, for all i ∈I,
ai ≤[PDF-GLYPH-U+0001]u = ui[PDF-GLYPH-U+0002].
In particular, the result holds if {ai : i ∈I} is an antichain.

```

## PDF page 054 | printed page 34

```text
34
BOOLEAN-VALUED MODELS OF SET THEORY
Proof We have [PDF-GLYPH-U+0001]u = ui[PDF-GLYPH-U+0002] = a ∧b, where
a =
[PDF-GLYPH-U+0006]
z∈dom(u)
[u(z) ⇒[PDF-GLYPH-U+0001]z ∈ui[PDF-GLYPH-U+0002]]
b =
[PDF-GLYPH-U+0006]
z∈dom(ui)
[ui(z) ⇒[PDF-GLYPH-U+0001]z ∈u[PDF-GLYPH-U+0002]].
If z ∈dom(u), then
ai ∧u(z) =
[PDF-GLYPH-U+0004]
j∈I
ai ∧aj ∧[PDF-GLYPH-U+0001]z ∈uj[PDF-GLYPH-U+0002]
≤
[PDF-GLYPH-U+0004]
j∈I
[PDF-GLYPH-U+0001]ui = uj[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]z ∈uj[PDF-GLYPH-U+0002]
(by(∗))
≤[PDF-GLYPH-U+0001]z ∈ui[PDF-GLYPH-U+0002],
so that ai ≤[u(z) ⇒[PDF-GLYPH-U+0001]z ∈ui[PDF-GLYPH-U+0002]] for any z ∈dom(u), whence ai ≤a. On the other
hand, if z ∈dom(ui), then
ai ∧ui(z) ≤ai ∧[PDF-GLYPH-U+0001]z ∈ui[PDF-GLYPH-U+0002] ≤u(z) ≤[PDF-GLYPH-U+0001]z ∈u[PDF-GLYPH-U+0002]
so that ai ≤[ui(z) ⇒[PDF-GLYPH-U+0001]z ∈u[PDF-GLYPH-U+0002]], whence ai ≤b. Hence ai ≤a ∧b, and the result
follows.
Problem 1.26 (Further properties of mixtures) Let {ai : i ∈I} be a
partition of unity in B.
(i) Let {xi : i ∈I} ⊆V be such that xi ̸= xj whenever i ̸= j. Show that there
is x ∈V (B) such that ai = [PDF-GLYPH-U+0001]x = ˆxi[PDF-GLYPH-U+0002] for all i ∈I.
(ii) Let {ui : i ∈I} ⊆V (B) and suppose that v ∈V (B) satisfies ai ≤[PDF-GLYPH-U+0001]v = ui[PDF-GLYPH-U+0002]
for all i ∈I. Show that V (B) |= v = [PDF-GLYPH-U+0001]
i∈I ai · ui.
Recall that in (1.10) we assigned a Boolean truth value to the formula ∃xφ(x)
by putting
[PDF-GLYPH-U+0001]∃xφ(x)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
u∈V (B)
[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002].
We now show, using the Mixing Lemma, that V (B) contains so many members
that the supremum on the right side of the above equality is actually attained
at some element u ∈V (B).

```

## PDF page 055 | printed page 35

```text
MIXTURES AND THE MAXIMUM PRINCIPLE
35
Lemma 1.27 (The Maximum Principle) If φ(x) is any B-formula, then
there is u ∈V (B) such that
[PDF-GLYPH-U+0001]∃xφ(x)[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002].
In particular, if V (B) |= ∃xφ(x), then V (B) |= φ(u) for some u ∈V (B).
Proof By (1.10) we have
[PDF-GLYPH-U+0001]∃xφ(x)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
u∈V (B)
[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002].
Since B is a set, so is {[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002] : u ∈V (B)} and the axiom of choice implies
that there is an ordinal α and a set {uξ
: ξ < α} ⊆V (B) such that
{[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002] : u ∈V (B)} = {[PDF-GLYPH-U+0001]φ(uξ)[PDF-GLYPH-U+0002] : ξ < α}. Accordingly,
[PDF-GLYPH-U+0001]∃xφ(x)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
ξ<α
[PDF-GLYPH-U+0001]φ(uξ)[PDF-GLYPH-U+0002].
For each ξ < α, put
aξ = [PDF-GLYPH-U+0001]φ(uξ)[PDF-GLYPH-U+0002] −
[PDF-GLYPH-U+0004]
η<ξ
[PDF-GLYPH-U+0001]φ(uη)[PDF-GLYPH-U+0002].
Then {aξ : ξ < α} is an antichain in B and aξ ≤[PDF-GLYPH-U+0001]φ(uξ)[PDF-GLYPH-U+0002] for all ξ < α. Put
u = [PDF-GLYPH-U+0001]
ξ<α aξ · uξ; then by the Mixing Lemma we have aξ ≤[PDF-GLYPH-U+0001]u = uξ[PDF-GLYPH-U+0002] for all
ξ < α. Also, clearly,
[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]∃xφ(x)[PDF-GLYPH-U+0002].
On the other hand,
[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002] ≥[PDF-GLYPH-U+0001]u = uξ[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]φ(uξ)[PDF-GLYPH-U+0002] ≥aξ
so that
[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002] ≥
[PDF-GLYPH-U+0004]
ξ<α
aξ =
[PDF-GLYPH-U+0004]
ξ<α
[PDF-GLYPH-U+0001]φ(uξ)[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]∃xφ(x)[PDF-GLYPH-U+0002].
Corollary 1.28 Let φ(x) be a B-formula such that V (B) |= ∃xφ(x).
(i) For any v ∈V (B) there is a u ∈V (B) such that [PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002] = 1 and [PDF-GLYPH-U+0001]φ(v)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002].

```

## PDF page 056 | printed page 36

```text
36
BOOLEAN-VALUED MODELS OF SET THEORY
(ii) If ψ(x) is a B-formula such that for any u ∈V (B), V (B) |= φ(u) implies
V (B) |= ψ(u), then V (B) |= ∀x[φ(x) →ψ(x)].
Proof (i) Apply the Maximum Principle to obtain w
∈
V (B) such that
[PDF-GLYPH-U+0001]φ(w)[PDF-GLYPH-U+0002] = 1, put b = [PDF-GLYPH-U+0001]φ(v)[PDF-GLYPH-U+0002] and u = b · v + b∗· w. Then
[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002] ≥[PDF-GLYPH-U+0001]u = v ∧φ(v)[PDF-GLYPH-U+0002] ∨[PDF-GLYPH-U+0001]u = w ∧φ(w)[PDF-GLYPH-U+0002] ≥b ∨b∗= 1,
and [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]φ(v)[PDF-GLYPH-U+0002]. Since [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] ≥b = [PDF-GLYPH-U+0001]φ(v)[PDF-GLYPH-U+0002] by
definition of u, the result follows.
(ii) Assume the hypothesis, and let v ∈V (B). Using (i), choose u ∈V (B)
such that [PDF-GLYPH-U+0001]φ(u)[PDF-GLYPH-U+0002] = 1 and [PDF-GLYPH-U+0001]φ(v)[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002]. Then [PDF-GLYPH-U+0001]ψ(u)[PDF-GLYPH-U+0002] = 1 and
[PDF-GLYPH-U+0001]φ(v)[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]ψ(u)[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]ψ(v)[PDF-GLYPH-U+0002].
The result follows.
Problem 1.29 (A variant of the Maximum Principle) Without using the
axiom of choice, show that, if V (B) |= ∃!xφ(x), then V (B) |= φ(u) for some
u ∈V (B). (Choose a sufficiently large ordinal α such that 1 = [PDF-GLYPH-U+0001]∃xφ(x)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0003]
x∈V (B)[PDF-GLYPH-U+0001]φ(x)[PDF-GLYPH-U+0002] and define u ∈V (B) by dom(u) = V (B)
α
, u(z) = [PDF-GLYPH-U+0001]∃x[φ(x) ∧
z ∈x[PDF-GLYPH-U+0002]].)
Problem 1.30 (The Maximum Principle is equivalent to the axiom of
choice)
(i) Let {ai : i ∈I} ⊆B satisfy Vi∈Iai = 1. A partition of unity {bi : i ∈I}
in B is called a disjoint refinement of {ai : i ∈I} if ∀i ∈I[bi ≤ai]. Define
u ∈V (B) by dom(u) = {ˆi : i ∈I}, u(ˆi) = ai for i ∈I. Let R be the set
of disjoint refinements of {ai : i ∈I} and U = {v ∈V (B) : [PDF-GLYPH-U+0001]v ∈u[PDF-GLYPH-U+0002] = 1}.
Show that the map {bi : i ∈I} [PDF-GLYPH-U+0017]→[PDF-GLYPH-U+0001]
i∈I bi · ˆi from R to U is one–one and
‘onto’ U in the sense that, for any v ∈U there is a unique {bi : i ∈I} ∈R
such that [PDF-GLYPH-U+0001][PDF-GLYPH-U+0001]
i∈I bi ·ˆi = v[PDF-GLYPH-U+0002] = 1.
(ii) Let ΣB be the assertion
∀u ∈V (B)[[PDF-GLYPH-U+0001]u ̸= Ø[PDF-GLYPH-U+0002] = 1 →∃v ∈V (B)[[PDF-GLYPH-U+0001]v ∈u[PDF-GLYPH-U+0002] = 1]]
(every nonempty B-valued set has an element) and ΠB the assertion: ‘for
any set, I, every I-indexed family of elements of B with join 1 has a
disjoint refinement’. Show without using the axiom of choice that ΣB and
ΠB are equivalent. (Use (i).) Deduce that the assertions ‘ΣB holds for every
complete Boolean algebra B’, and ‘the Maximum Principle holds in V (B)
for every complete Boolean algebra B’ are each equivalent to the axiom of

```

## PDF page 057 | printed page 37

```text
THE TRUTH OF THE AXIOMS OF SET THEORY IN V (B)
37
choice. (Confine attention to the case in which B is of the form PX for an
arbitrary set X.)
We conclude this section by introducing the notion of a core of a
Boolean-valued set. Let u ∈V (B). A set v ⊆V (B) is called a core for u if
the following conditions are satisfied:(i) [PDF-GLYPH-U+0001]x ∈u[PDF-GLYPH-U+0002] = 1 for all x ∈v, (ii) for each
y ∈V (B) such that [PDF-GLYPH-U+0001]y ∈u[PDF-GLYPH-U+0002] = 1 there is a unique x ∈v such that [PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002] = 1.
Thus a core for u represents the class of B -valued objects, which are elements
of u with probability 1.
Lemma 1.31 Any u ∈V (B) has a core.
Proof For each x ∈V (B) put
fx = {⟨z, u(z) ∧[PDF-GLYPH-U+0001]z = x[PDF-GLYPH-U+0002]⟩: z ∈dom(u)}.
Using the axiom of replacement we can find a set w ⊆V (B) such that for each
x ∈V (B) there is y ∈w for which fx = fy. Now let v be a set obtained by
selecting one memeber from each ∼-equivalence class in the set {x ∈w : [PDF-GLYPH-U+0001]x ∈
u[PDF-GLYPH-U+0002] = 1}, where ∼is defined by x ∼y ↔[PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002] = 1. It is easily verified that v
is a core for u.
Note that a core of a B-valued set is unique up to bijection in the sense that
there is a bijection between any pair of such cores. Observe also that, if u is a
B-valued set the that V (B) |= u ̸= Ø, then the Maximum Principle implies that
any core of u us nonempty.
The following result, which will prove useful later on, is an immediate
consequence of Corollary 1.28.
Lemma 1.32 Suppose that u ∈V (B) is such that V (B) |= u ̸= ∅and let v be a
core for u. Then for any x ∈V (B) there is y ∈v such that [PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]x ∈u[PDF-GLYPH-U+0002].
The truth of the axioms of set theory in V (B)
We are now going to show that all of the axioms of ZFC are true in V (B) for
any complete Boolen algebra B. (This result is usually expressed by saying that
V (B) is a Boolean valued model of ZFC.) We do this by proving in ZFC that
V (B) |= σ for each axiom of ZFC.
Theorem 1.33 All the axioms—and hence all the theorems—of ZFC are true
in V (B).
We prove this theorem by means of a sequence of lemmas.
Lemma 1.34 The axiom of extensionality is true in V (B).
Proof This follows immediately from (1.16) and 1.18 (ii).

```

## PDF page 058 | printed page 38

```text
38
BOOLEAN-VALUED MODELS OF SET THEORY
Lemma 1.35 The axiom scheme of separation is true in V (B).
Proof Recall that the scheme in question is
∀u∃v∀x[x ∈v ↔x ∈u ∧ψ(x)].
To see that each instance is true in V (B), let u ∈V (B), define v ∈V (B) by
dom(v) = dom(u) and, for x ∈dom(v),
v(x) = u(x) ∧[PDF-GLYPH-U+0001]ψ(x)[PDF-GLYPH-U+0002].
Then
[PDF-GLYPH-U+0001]∀x[x ∈v ↔x ∈u ∧ψ(x)][PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]∀x ∈v[x ∈u ∧ψ(x)][PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]∀x ∈u[ψ(x) →x ∈v][PDF-GLYPH-U+0002].
Now
[PDF-GLYPH-U+0001]∀x ∈v[x ∈u ∧ψ(x)][PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0006]
x∈dom(v)
[[u(x) ∧[PDF-GLYPH-U+0001]ψ(x)[PDF-GLYPH-U+0002]] ⇒[[PDF-GLYPH-U+0001]x ∈u[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]ψ(x)[PDF-GLYPH-U+0002]]] = 1,
using 1.17(ii). Similarly,
[PDF-GLYPH-U+0001]∀x ∈u[ψ(x) →x ∈v][PDF-GLYPH-U+0002] = 1,
and the assertion follows.
Lemma 1.36 The axiom scheme of replacement is true in V (B).
Proof Recall that this is the scheme
∀u[∀x ∈y∃yφ(x, y) →∃v∀x ∈u∃y ∈vφ(x, y)].
To show that each instance is true in V (B), notice that, for u ∈V (B) we have
[PDF-GLYPH-U+0001]∀x ∈u∃yφ(x, y)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0006]
x∈dom(u)
[u(x) ⇒[PDF-GLYPH-U+0001]∃yφ(x, y)[PDF-GLYPH-U+0002]]
=
[PDF-GLYPH-U+0006]
x∈dom(u)

u(x) ⇒
[PDF-GLYPH-U+0004]
y∈V (B)
[PDF-GLYPH-U+0001]φ(x, y)[PDF-GLYPH-U+0002]

.
(1)

```

## PDF page 059 | printed page 39

```text
THE TRUTH OF THE AXIOMS OF SET THEORY IN V (B)
39
Since B is a set, we may invoke the axiom of replacement in V to obtain a map
x [PDF-GLYPH-U+0017]→αx with domain dom(u) and range a set of ordinals such that, for each
x ∈dom(u),
[PDF-GLYPH-U+0004]
y∈V (B)
[PDF-GLYPH-U+0001]φ(x, y)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
y∈V (B)
ax
[PDF-GLYPH-U+0001]φ(x, y)[PDF-GLYPH-U+0002].
(2)
Let α = [PDF-GLYPH-U+0015]{αx : x ∈dom(u)}. Then, by (2),
[PDF-GLYPH-U+0006]
x∈dom(u)

u(x) ⇒
[PDF-GLYPH-U+0004]
y∈V (B)
[PDF-GLYPH-U+0001]φ(x, y)[PDF-GLYPH-U+0002]

=
[PDF-GLYPH-U+0006]
x∈dom(u)

u(x) ⇒
[PDF-GLYPH-U+0004]
y∈V (B)
αx
[PDF-GLYPH-U+0001]φ(x, y)[PDF-GLYPH-U+0002]


(3)
≤
[PDF-GLYPH-U+0006]
x∈dom(u)

u(x) ⇒
[PDF-GLYPH-U+0004]
y∈V (B)
α
[PDF-GLYPH-U+0001]φ(x, y)[PDF-GLYPH-U+0002]

.
Now put v = V (B)
α
× {1}; then v ∈V (B) and
[PDF-GLYPH-U+0004]
y∈V (B)
α
[PDF-GLYPH-U+0001]φ(x, y)[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]∃y ∈vφ(x, y)[PDF-GLYPH-U+0002].
Hence, by (1) and (3),
[PDF-GLYPH-U+0001]∀x ∈u∃yφ(x, y)[PDF-GLYPH-U+0002] ≤
[PDF-GLYPH-U+0006]
x∈dom(u)
[u(x) ⇒[PDF-GLYPH-U+0001]∃y ∈vφ(x, y)[PDF-GLYPH-U+0002]]
= [PDF-GLYPH-U+0001]∀x ∈u∃y ∈vφ(x, y)[PDF-GLYPH-U+0002].
The truth of the axiom scheme of replacement in V (B) follows.
Lemma 1.37 The axiom of union is true in V (B).
Proof This is the sentence
∀u∃v∀x[x ∈v ↔∃y ∈u[x ∈y]].
To verify its truth in V (B), let u ∈V (B); define v ∈V (B) so that dom(v) =
[PDF-GLYPH-U+0015]{dom(y) : y ∈dom(u)} and
v(x) = [PDF-GLYPH-U+0001]∃y ∈u[x ∈y][PDF-GLYPH-U+0002]

```

## PDF page 060 | printed page 40

```text
40
BOOLEAN-VALUED MODELS OF SET THEORY
for x ∈dom(v). Then
[PDF-GLYPH-U+0001]∀x ∈v∃y ∈u[x ∈y][PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0006]
x∈dom(v)
[[PDF-GLYPH-U+0001]∃y ∈u[x ∈y][PDF-GLYPH-U+0002] ⇒[PDF-GLYPH-U+0001]∃y ∈u[x ∈y][PDF-GLYPH-U+0002]] = 1.
Also,
[PDF-GLYPH-U+0001]∀y ∈u∀x ∈y[x ∈v][PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0006]
y∈dom(u)

u(y) ⇒
[PDF-GLYPH-U+0006]
x∈dom(y)
[y(x) ⇒[PDF-GLYPH-U+0001]x ∈v[PDF-GLYPH-U+0002]]


=
[PDF-GLYPH-U+0006]
y∈dom(u)
[PDF-GLYPH-U+0006]
x∈dom(y)
[u(y) ∧y(x) ⇒[PDF-GLYPH-U+0001]x ∈v[PDF-GLYPH-U+0002]]
= a, say.
Since x ∈dom(y) and y ∈dom(u) →x ∈dom(v), we have [PDF-GLYPH-U+0001]x ∈v[PDF-GLYPH-U+0002] ≥v(x) for
x ∈dom(y). Also, for x ∈dom(y) and y ∈dom(u) we have
u(y) ∧y(x) ≤u(y) ∧[PDF-GLYPH-U+0001]x ∈y[PDF-GLYPH-U+0002]
≤
[PDF-GLYPH-U+0004]
y∈dom(u)
[u(y) ∧[PDF-GLYPH-U+0001]x ∈y[PDF-GLYPH-U+0002]]
= [PDF-GLYPH-U+0001]∃y ∈u[x ∈y][PDF-GLYPH-U+0002]
= v(x).
Putting these facts together, we see that
a ≥
[PDF-GLYPH-U+0006]
y∈dom(u)
[PDF-GLYPH-U+0006]
x∈dom(y)
[v(x) ⇒v(x)] = 1
and the result follows.
Lemma 1.38 The power set axiom is true in V (B)
Proof This is the sentence
∀u∃v∀x[x ∈v ↔∀y ∈x[y ∈u]].
To establish its truth in V (B), let u ∈V (B) and define v ∈V (B) by
dom(v) = Bdom(u)

```

## PDF page 061 | printed page 41

```text
THE TRUTH OF THE AXIOMS OF SET THEORY IN V (B)
41
and, for x ∈dom(v),
v(x) = [PDF-GLYPH-U+0001]x ⊆u[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]∀y ∈x[y ∈u][PDF-GLYPH-U+0002].
It suffices to show that
[PDF-GLYPH-U+0001]∀x[x ∈v ↔x ⊆u][PDF-GLYPH-U+0002] = 1.
First, we note that
[PDF-GLYPH-U+0001]∀x ∈v[x ⊆v][PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0006]
x∈dom(v)
[v(x) ⇒[PDF-GLYPH-U+0001]x ⊆u[PDF-GLYPH-U+0002]]
=
[PDF-GLYPH-U+0006]
x∈dom(v)
[v(x) ⇒v(x)]
= 1.
It remains to show that
[PDF-GLYPH-U+0001]∀x[x ⊆u →x ∈v][PDF-GLYPH-U+0002] = 1.
(1)
Given x ∈V (B), define x′ ∈V (B) by dom(x′) = dom(u) and x′(y) = [PDF-GLYPH-U+0001]y ∈x[PDF-GLYPH-U+0002] for
y ∈dom(x′). Notice that x′ ∈dom(v). We show that
[PDF-GLYPH-U+0001]x ⊆u →x = x′[PDF-GLYPH-U+0002] = 1
(2)
and
[PDF-GLYPH-U+0001]x ⊆u →x′ ∈v[PDF-GLYPH-U+0002] = 1,
(3)
from which it will follow immediately that
[PDF-GLYPH-U+0001]x ⊆u →x ∈v[PDF-GLYPH-U+0002] = 1,
which yields (1).
We observe that, for any y ∈V (B),
[PDF-GLYPH-U+0001]y ∈x′[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
z∈dom(u)
[x′(z) ∧[PDF-GLYPH-U+0001]z = y[PDF-GLYPH-U+0002]]
=
[PDF-GLYPH-U+0004]
z∈dom(u)
[[PDF-GLYPH-U+0001]z ∈x[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]z = y[PDF-GLYPH-U+0002]] ≤[PDF-GLYPH-U+0001]y ∈x[PDF-GLYPH-U+0002].

```

## PDF page 062 | printed page 42

```text
42
BOOLEAN-VALUED MODELS OF SET THEORY
Therefore
[PDF-GLYPH-U+0001]x′ ⊆x[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]∀y[y ∈x′ →y ∈x][PDF-GLYPH-U+0002] = 1.
(4)
Next, for any y ∈V (B) we have
[PDF-GLYPH-U+0001]y ∈u ∧y ∈x[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
z∈dom(u)
[u(z) ∧[PDF-GLYPH-U+0001]y = z[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]y ∈x[PDF-GLYPH-U+0002]]
≤
[PDF-GLYPH-U+0004]
z∈dom(u)
[[PDF-GLYPH-U+0001]y = z[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]z ∈x[PDF-GLYPH-U+0002]]
=
[PDF-GLYPH-U+0004]
z∈dom(u)
[[PDF-GLYPH-U+0001]y = z[PDF-GLYPH-U+0002] ∧x′(z)]
= [PDF-GLYPH-U+0001]y ∈x′[PDF-GLYPH-U+0002],
so that [PDF-GLYPH-U+0001]u ∩x ⊆x′[PDF-GLYPH-U+0002] = 1. Hence, using this and (4), we get
[PDF-GLYPH-U+0001]x ⊆u[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]u ∩x ⊆x′ ∧x′ ⊆x ∧x ⊆u[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]x = x′[PDF-GLYPH-U+0002],
which gives (2).
Finally we prove (3). We have
[PDF-GLYPH-U+0001]x ⊆u[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]∀y[y ∈x →y ∈u][PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0006]
y∈V (B)
[[PDF-GLYPH-U+0001]y ∈x[PDF-GLYPH-U+0002] ⇒[PDF-GLYPH-U+0001]y ∈u[PDF-GLYPH-U+0002]]
≤
[PDF-GLYPH-U+0006]
y∈dom(x′)
[x′(y) ⇒[PDF-GLYPH-U+0001]y ∈u[PDF-GLYPH-U+0002]]
= [PDF-GLYPH-U+0001]∀y ∈x′[y ∈u][PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]x′ ⊆u[PDF-GLYPH-U+0002] = v(x′) ≤[PDF-GLYPH-U+0001]x′ ∈v[PDF-GLYPH-U+0002],
since x′ ∈dom(v). This immediately gives (3), completing the proof.

```

## PDF page 063 | printed page 43

```text
THE TRUTH OF THE AXIOMS OF SET THEORY IN V (B)
43
In connection with the proof of Lemma 1.38, we make the following
Definition 1.39 For u ∈V (B) we define P (B)(u) to be that element v ∈V (B)
such that dom(v) = Bdom(u) and, for x ∈dom(v), v(x) = [PDF-GLYPH-U+0001]x ⊆u[PDF-GLYPH-U+0002]. P (B)(u)
is called the power set of u in V (B); the proof of Lemma 1.38 shows that it
satisfies
V (B) |= P (B)(u) = Pu.
Problem 1.40 (Definite sets) An element u ∈V (B) is said to be definite if
u(x) = 1 for all x ∈dom(u). Let u ∈V (B) be definite, and define w ∈V (B) by
w = Bdom(u) × {1}. Show that
[PDF-GLYPH-U+0001]∀x[x ∈w ↔x ⊆u][PDF-GLYPH-U+0002] = 1.
(Use Definition 1.39.) Thus, if u is definite, the simple object Bdom(u) × {1} also
serves as the power set of u in V (B).
Lemma 1.41 The axiom of infinity is true in V (B).
Proof The axiom in question is the sentence ∃uφ(u), where φ(u) is the formula
∅∈u ∧∀x ∈u∃y ∈u(x ∈y).
Now φ(u) is obviously a restricted formula, and we certainly have φ(ω). Hence,
by Theorem 1.23 (v), we get [PDF-GLYPH-U+0001]φ(ˆω)[PDF-GLYPH-U+0002] = 1, and so [PDF-GLYPH-U+0001]∃uφ(u)[PDF-GLYPH-U+0002] = 1.
Lemma 1.42 The axiom of regularity is true in V (B).
Proof The axiom scheme in question is
∀x[∀y ∈xφ(y) →φ(x)] →∀xφ(x).
To see that each instance is true in V (B), first put
b = [PDF-GLYPH-U+0001]∀x[∀y ∈xφ(y) →φ(x)][PDF-GLYPH-U+0002].
It now suffices to show that, for any x ∈V (B),
b ≤[PDF-GLYPH-U+0001]φ(x)[PDF-GLYPH-U+0002].

```

## PDF page 064 | printed page 44

```text
44
BOOLEAN-VALUED MODELS OF SET THEORY
We apply the induction principle for V (B) (1.7). Assume for y ∈dom(x) that
b ≤[PDF-GLYPH-U+0001]φ(y)[PDF-GLYPH-U+0002]. Then
b ≤
[PDF-GLYPH-U+0006]
y∈dom(x)
[PDF-GLYPH-U+0001]φ(y)[PDF-GLYPH-U+0002] ≤
[PDF-GLYPH-U+0006]
y∈dom(x)
[x(y) ⇒[PDF-GLYPH-U+0001]φ(y)[PDF-GLYPH-U+0002]]
= [PDF-GLYPH-U+0001]∀y ∈xφ(y)[PDF-GLYPH-U+0002].
But
b ≤[[PDF-GLYPH-U+0001]∀y ∈xφ(y)[PDF-GLYPH-U+0002] ⇒[PDF-GLYPH-U+0001]φ(x)[PDF-GLYPH-U+0002]],
so that
b ≤[[PDF-GLYPH-U+0001]∀y ∈xφ(y)[PDF-GLYPH-U+0002] ⇒[PDF-GLYPH-U+0001]φ(x)[PDF-GLYPH-U+0002]] ∧[PDF-GLYPH-U+0001]∀y ∈xφ(y)[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]φ(x)[PDF-GLYPH-U+0002],
as required.
In order to verify the axiom of choice in V (B) it suffices to verify the set-
theoretically equivalent principle Zorn’s lemma. Recall that a partially ordered
set is said to be inductive if chains (i.e. linearly ordered subsets) in it have upper
bounds and Zorn’s lemma states that any nonempty inductive partially ordered
set has a maximal element.
So finally we prove
Lemma 1.43 Zorn’s lemma, and hence the axiom of choice, is true in V (B).
Proof By Corollary 1.28(ii), it is enough to show that, for any X, ≤X∈V (B), if
V (B) |= ⟨X, ≤X⟩is a nonempty inductive partially ordered set then V (B) |=
⟨X, ≤X⟩has a maximal element. Suppose then that the antecedent of this
implication holds. Let Y be a core for X and define the relation ≤Y on Y by
y ≤Y y′ ↔[PDF-GLYPH-U+0001]y ≤X y′[PDF-GLYPH-U+0002] = 1
for y, y′ ∈Y . It is easy to verify that ≤Y is a partial ordering on Y ; we claim
that with this partial ordering Y is inductive. For let C be any chain in Y . It is
readily shown that C′ = C × {1} ∈V (B) satisfies
V (B) |= C′is a chain in X.
Accordingly, by the Maximum Principle there is u ∈V (B) for which
V (B) |= u is an upper bound for C′in X.

```

## PDF page 065 | printed page 45

```text
ORDINALS AND CONSTRUCTIBLE SETS IN V (B)
45
Now choose w ∈Y such that [PDF-GLYPH-U+0001]w = u[PDF-GLYPH-U+0002] = 1. Then w is an upper bound for C
in Y . For if x ∈C, then clearly [PDF-GLYPH-U+0001]x ∈C′[PDF-GLYPH-U+0002] = 1, whence [PDF-GLYPH-U+0001]x ≤X u[PDF-GLYPH-U+0002] = 1 so that
[PDF-GLYPH-U+0001]x ≤X w[PDF-GLYPH-U+0002] = 1, and x ≤Y w.
Therefore Y is inductive as claimed. By Zorn’s lemma in V, Y has a maximal
element c. Then [PDF-GLYPH-U+0001]c ∈X[PDF-GLYPH-U+0002] = 1; we claim further that
V (B) |= c is a maximal element of X.
(1)
To prove this, take x ∈V (B) and apply Lemma 1.32 to obtain y ∈Y for which
[PDF-GLYPH-U+0001]x ∈X[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002]. Then
[PDF-GLYPH-U+0001]c ≤X x ∧x ∈X[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]c ≤X x ∧x = y[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]c ≤X y[PDF-GLYPH-U+0002].
(2)
Now let v = y · a + c · a∗, where a = [PDF-GLYPH-U+0001]c ≤X y[PDF-GLYPH-U+0002]. Then [PDF-GLYPH-U+0001]v ∈X[PDF-GLYPH-U+0002] = 1 and so there
is z ∈Y for which [PDF-GLYPH-U+0001]v = z[PDF-GLYPH-U+0002] = 1. It is easily shown that [PDF-GLYPH-U+0001]c ≤X v[PDF-GLYPH-U+0002] = 1, whence
[PDF-GLYPH-U+0001]c ≤X z[PDF-GLYPH-U+0002] = 1, and so c ≤Y z. Hence c = z by the maximality of c. Therefore
[PDF-GLYPH-U+0001]c ≤X y[PDF-GLYPH-U+0002] = a ≤[PDF-GLYPH-U+0001]y = v[PDF-GLYPH-U+0002]
≤[PDF-GLYPH-U+0001]y = v[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]v = z[PDF-GLYPH-U+0002]
≤[PDF-GLYPH-U+0001]y = z[PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]y = c[PDF-GLYPH-U+0002],
and so by (2)
[PDF-GLYPH-U+0001]c ≤X x ∧x ∈X[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]y = c[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]x ∈X[PDF-GLYPH-U+0002]
≤[PDF-GLYPH-U+0001]y = c[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002]
≤[PDF-GLYPH-U+0001]x = c[PDF-GLYPH-U+0002].
Thus
V (B) |= ∀x ∈X[c ≤X x →x = c]
that is, (1). This completes the proof.
The proof of Theorem 1.33 is now complete.
Ordinals and constructible sets in V (B)
Since the formula Ord(x) is restricted, it follows from Theorem 1.23(v) that
[PDF-GLYPH-U+0001]Ord(ˆα)[PDF-GLYPH-U+0002] = 1 for every ordinal α. It is natural to call members of V (B) of the
form ˆα standard ordinals in V (B). Our next result relates the property of being
an (arbitrary) ordinal in V (B) to that of being a standard ordinal.

```

## PDF page 066 | printed page 46

```text
46
BOOLEAN-VALUED MODELS OF SET THEORY
Theorem 1.44 For all u ∈V (B),
[PDF-GLYPH-U+0001]Ord(u)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
α∈ORD
[PDF-GLYPH-U+0001]u = ˆα[PDF-GLYPH-U+0002].
Proof Since [PDF-GLYPH-U+0001]Ord(ˆα)[PDF-GLYPH-U+0002] = 1, we have
[PDF-GLYPH-U+0001]u = ˆα[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]u = ˆα[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]Ord(ˆα)[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]Ord(u)[PDF-GLYPH-U+0002].
Hence
[PDF-GLYPH-U+0004]
α∈ORD
[PDF-GLYPH-U+0001]u = ˆα[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]Ord(u)[PDF-GLYPH-U+0002].
To establish the reverse inequality, first observe that, since [PDF-GLYPH-U+0001]ˆη = ˆξ[PDF-GLYPH-U+0002] = 0
whenever η ̸= ξ (by Theorem 1.23(ii)), the map ξ [PDF-GLYPH-U+0017]→[PDF-GLYPH-U+0001]x = ˆξ[PDF-GLYPH-U+0002] is one–one from
Dx = {ξ: [PDF-GLYPH-U+0001]x = ˆξ[PDF-GLYPH-U+0002] ̸= 0}
into B whenever x ∈dom(u). Since B is a set, so therefore is Dx. Put
D =
[PDF-GLYPH-U+0005]
x∈dom(u)
Dx.
If α0 is any ordinal greater than every ordinal in D, we have [PDF-GLYPH-U+0001]ˆα0 = x[PDF-GLYPH-U+0002] = 0 for
any x ∈dom(u). Hence
[PDF-GLYPH-U+0001]ˆα0 ∈u[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
x∈dom(u)
[u(x) ∧[PDF-GLYPH-U+0001]ˆα0 = x[PDF-GLYPH-U+0002]] = 0.
A standard theorem of ZF asserts that Ord(u)∧Ord(v) →u ∈v ∨u = v ∨v ∈u;
hence
[PDF-GLYPH-U+0001]Ord(u)[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]u ∈ˆα0[PDF-GLYPH-U+0002] ∨[PDF-GLYPH-U+0001]u = ˆα0[PDF-GLYPH-U+0002] ∨[PDF-GLYPH-U+0001]ˆα0 ∈u[PDF-GLYPH-U+0002].
Since [PDF-GLYPH-U+0001]ˆα0 ∈u[PDF-GLYPH-U+0002] = 0, it follows that
[PDF-GLYPH-U+0001]Ord(u)[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]u ∈ˆα0[PDF-GLYPH-U+0002] ∨[PDF-GLYPH-U+0001]u = ˆα0[PDF-GLYPH-U+0002] ≤
[PDF-GLYPH-U+0004]
α∈ORD
[PDF-GLYPH-U+0001]u = ˆα[PDF-GLYPH-U+0002].

```

## PDF page 067 | printed page 47

```text
ORDINALS AND CONSTRUCTIBLE SETS IN V (B)
47
Problem 1.45 (Boolean-valued ordinals)
(i) Show that, for any formula φ(x), [PDF-GLYPH-U+0001]∃αφ(α)[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0003]
α[PDF-GLYPH-U+0001]φ(ˆα)[PDF-GLYPH-U+0002] and [PDF-GLYPH-U+0001]∀αφ(α)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0002]
α[PDF-GLYPH-U+0001]φ(ˆα[PDF-GLYPH-U+0002]. Thus, quantifications over ordinals in V (B) can be replaced by
suprema and infima in B over standard ordinals.
(ii) Show that the following conditions on u ∈V (B) are equivalent:
(a) [PDF-GLYPH-U+0001]Ord(u)[PDF-GLYPH-U+0002] = 1;
(b) there is a set A of ordinals and a partition of unity {aξ: ξ ∈A} in B
such that [PDF-GLYPH-U+0001]u = Σξ∈Aaξ · ˆξ[PDF-GLYPH-U+0002] = 1.
Thus the ordinals of V (B) are precisely the mixtures of standard ordinals.
Formulate and prove a similar result for the ‘natural numbers in V (B)’.
The situation for constructible sets in V (B) is similar to that for ordinals. In
fact, we have the following theorem.
Theorem 1.46 For all u ∈V (B),
[PDF-GLYPH-U+0001]L(u)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
x∈L
[PDF-GLYPH-U+0001]u = ˆx[PDF-GLYPH-U+0002].
Proof Let Lα be the αth constructible level. Then, using Problem 1.45, we have
[PDF-GLYPH-U+0001]L(u)[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]∃α(u ∈Lα)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
α∈ORD
[PDF-GLYPH-U+0001]u ∈Lˆα[PDF-GLYPH-U+0002].
Now the formula x = Lα is Σ1 (by a well-known result of set theory) so
Problem 1.24 gives
x = Lα →[PDF-GLYPH-U+0001]ˆx = Lˆα[PDF-GLYPH-U+0002] = 1,
that is
[PDF-GLYPH-U+0001]ˆLα = Lˆα[PDF-GLYPH-U+0002] = 1.
Therefore
[PDF-GLYPH-U+0001]L(u)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
α∈ORD
[PDF-GLYPH-U+0001]u ∈Lˆα[PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0004]
α∈ORD
[PDF-GLYPH-U+0001]u ∈ˆLα[PDF-GLYPH-U+0002]

```

## PDF page 068 | printed page 48

```text
48
BOOLEAN-VALUED MODELS OF SET THEORY
=
[PDF-GLYPH-U+0004]
α∈ORD
[PDF-GLYPH-U+0004]
x∈Lα
[PDF-GLYPH-U+0001]u = ˆx[PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0004]
x∈L
[PDF-GLYPH-U+0001]u = ˆx[PDF-GLYPH-U+0002],
which is the required result.
It follows immediately form this theorem that, if V ̸= L, then [PDF-GLYPH-U+0001]V ̸= L[PDF-GLYPH-U+0002] = 1.
Problem 1.47 (Boolean-valued constructible sets) State and prove, for
constructible sets, results parallel to those give in Problem 1.45.
Cardinals in V (B)
We recall that, for each set x, |x| denotes the cardinality of x. Since the formula
|x| = |y| is easily seen to be Σ1, it follows immediately from Problem 1.24 that
|x| = |y| →V (B) |= |ˆx| = |ˆy|.
(1.48)
We shall see later on that the converse does not hold in general.
Theorem 1.49
(i) V (B) |= ˆℵ0 = ℵ0.
(ii) For all α,
V (B) |= ˆℵα ≤ℵˆα.
Proof (i) The formula x = ℵ0 is restricted, so the result in question follows easily
from Theorem 1.23(v).
(ii) is proved by induction on α. For α = 0 the result follows immediately
from (i). Suppose now that α > 0 and
V (B) |= ˆℵβ ≤ℵˆβ
(1)
for all β < α. Then we have
ℵ0 ≤ξ < ℵα →|ξ| = ℵβ for some β < α
→V (B) |= |ˆξ| = |ˆℵβ|
(by1.48)
→V (B) |= |ˆξ| ≤ℵˆβ
(by (1))
→V (B) |= |ˆξ| < ℵˆα
→V (B) |= ˆξ < ℵˆα.

```

## PDF page 069 | printed page 49

```text
CARDINALS IN V (B)
49
Also,
ξ < ℵ0 →V (B) |= ˆξ < ˆℵ0
→V (B) |= ˆξ < ℵˆα.
Hence
ξ < ℵα →V (B) |= ˆξ < ℵˆα.
(2)
Thus
[PDF-GLYPH-U+0001]η < ˆℵα[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
ξ<ℵα
[PDF-GLYPH-U+0001]η = ˆξ[PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0004]
ξ<ℵα
[[PDF-GLYPH-U+0001]η = ˆξ[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]ˆξ < ℵˆα[PDF-GLYPH-U+0002]]
(by(2))
≤[PDF-GLYPH-U+0001]η < ℵˆα[PDF-GLYPH-U+0002].
Therefore
V (B) |= ∀η[η < ˆℵα →η < ℵˆα],
whence
V (B) |= ˆℵα ≤ℵˆα.
This completes the induction step, and the proof.
Let Card(α) be the formula which asserts that α is a cardinal. Then we have
Theorem 1.50
(i) V (B) |= Card(ˆα) for any α ≤ω.
(ii) If V (B) |= Card(ˆα), then Card(α).
Proof (i) For α = ω we already know that V (B) |= Card(ˆα) by Theorem 1.49 (i).
On the other hand, it is a theorem of ZF that ∀α[α ∈ω →Card(α)]. Hence
V (B) |= ∀α[α ∈ω →Card(α)].
But V (B) |= ˆω = ω by 1.49 (i), so that
V (B) |= ∀α[α ∈ˆω →Card(α)].
Hence [PDF-GLYPH-U+0002]
α∈ω[PDF-GLYPH-U+0001]Card(ˆα)[PDF-GLYPH-U+0002] = 1, and (i) follows.
(ii) Notice that ¬Card(α) is a Σ1-formula, and apply Problem 1.24.

```

## PDF page 070 | printed page 50

```text
50
BOOLEAN-VALUED MODELS OF SET THEORY
The formula Card(x) is not Σ1, so the converse of Theorem 1.50(ii) may fail,
that is, the property of being a cardinal is not in general preserved under the
passage from V to V (B) (cf. Chapter 5). However, there is a simple condition on
B which ensures that this property is preserved.
A Boolean algebra is said to satisfy the countable chain condition (ccc) if
every antichain in it is countable. (It would seem more reasonable to call this the
countable antichain condition but the present terminology has the sanction of
tradition.)
Complete Boolean algebras satisfying the ccc are readily obtained as follows.
Let I be any set and let 2I have the product topology, where 2 is assigned the
discrete topology. Then, as is well-known (e.g. see Kelley 1955, prob. 5 O(f)), any
family of disjoint open sets in 2I is countable, so a fortiori RO(2I) satisfies ccc.
We now show that cardinals behave very well in V (B) when B satisfies ccc.
Theorem 1.51 Suppose that B satisfies ccc. Then, for any α, and any
x, y ∈V ,
(i) Card(α) →V (B) |= Card(ˆα);
(ii) V (B) |= ˆℵα = ℵˆα;
(iii) |x| = |y| ↔V (B) |= |ˆx| = |ˆy|;
(iv) Card(α) ∧α is regular →V (B) |= ˆα is regular;
(v) if α is an uncountable regular cardinal, and ξ ∈V (B) satisfies [PDF-GLYPH-U+0001]ξ < ˆα[PDF-GLYPH-U+0002] = 1,
then there is an ordinal β < α such that [PDF-GLYPH-U+0001]ξ < ˆβ[PDF-GLYPH-U+0002] = 1.
Proof (i) Let α be a cardinal. If α ≤ω then V (B) |= Card(ˆα) by Theorem 1.50(i),
so we may suppose that α > ω. To obtain the required conclusion it suffices to
show that, for all f ∈V (B) and all β < α,
[PDF-GLYPH-U+0001]Fun(f) ∧dom(f) = ˆβ ∧ran(f) = ˆα[PDF-GLYPH-U+0002] = 0.
Suppose on the contrary that, for some f ∈V (B) and β < α we have
a = [PDF-GLYPH-U+0001]Fun(f) ∧dom(f) = ˆβ ∧ran(f) = ˆα[PDF-GLYPH-U+0002] ̸= 0;
then
0 ̸= a ≤
[PDF-GLYPH-U+0006]
η<α
[PDF-GLYPH-U+0004]
ξ<β
[PDF-GLYPH-U+0001]f(ˆξ) = ˆη[PDF-GLYPH-U+0002] ∧a.
It follows that for each η < α there is a least ξη < β such that
[PDF-GLYPH-U+0001]f(ˆξη) = ˆη[PDF-GLYPH-U+0002] ∧a ̸= 0.

```

## PDF page 071 | printed page 51

```text
CARDINALS IN V (B)
51
Since α is an uncountable cardinal and β < α there must exist a γ < β such
that the set
X = {η < α : ξη = γ}
is uncountable. It follows immediately that the set
{[PDF-GLYPH-U+0001]f(ˆγ) = ˆη[PDF-GLYPH-U+0002] ∧a : η ∈X}
is an uncountable antichain in B, contradicting ccc. Hence a = 0 and (i) follows.
(ii) This goes by induction on α. Assuming that V (B) |= ˆℵβ = ℵˆβ for all
β < α, by Theorem 1.49(ii) it suffices to show that
V (B) |= ℵˆα ≤ˆℵα.
By (i), we have V (B) |= Card(ˆℵα). Also, if β < α, then V (B) |= ˆℵβ < ˆℵα and by
inductive hypothesis V (B) |= ˆℵβ = ℵˆβ. Hence V (B) |= ℵˆβ < ˆℵα, so that
1 = [PDF-GLYPH-U+0001]Card(ˆℵα)[PDF-GLYPH-U+0002] ∧
[PDF-GLYPH-U+0006]
β<α
[PDF-GLYPH-U+0001]ℵˆβ < ˆℵα[PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]Card(ˆℵα) ∧∀β < ˆα(ℵβ < ˆℵα)[PDF-GLYPH-U+0002]
≤[PDF-GLYPH-U+0001]ℵˆα ≤ˆℵα[PDF-GLYPH-U+0002],
completing the induction step, and proving (ii).
(iii) is an immediate consequence of (ii).
(iv) Let α be a regular cardinal; without loss of generality we may assume
α > ℵ0. Suppose that the conclusion is false, that is, [PDF-GLYPH-U+0001]ˆα is not regular[PDF-GLYPH-U+0002] ̸= 0. Let
φ(x, y) be the statement Fun(x) ∧dom(x) = y and ran(x) is cofinal in ˆα. Then
0 ̸= [PDF-GLYPH-U+0001]ˆα is not regular[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]∃ξ < ˆα∃fφ(f, ξ)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
β<α
[PDF-GLYPH-U+0001]∃fφ(f, ˆβ)[PDF-GLYPH-U+0002].
Hence there is β < α such that
0 ̸= [PDF-GLYPH-U+0001]∃fφ(f, ˆβ)[PDF-GLYPH-U+0002] = a, say,
and so the Maximum Principle yields an f ∈V (B) for which a = [PDF-GLYPH-U+0001]φ(f, β)[PDF-GLYPH-U+0002]. Then
0 ̸= a ≤[PDF-GLYPH-U+0001]ran(f) is cofinal in ˆα[PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0006]
η<α
[PDF-GLYPH-U+0004]
ξ<β
[PDF-GLYPH-U+0004]
µ≥η
[PDF-GLYPH-U+0001]f(ˆξ) = ˆµ[PDF-GLYPH-U+0002].

```

## PDF page 072 | printed page 52

```text
52
BOOLEAN-VALUED MODELS OF SET THEORY
It follows that for each η < α there are ordinals ξη < β, µη < α such that
[PDF-GLYPH-U+0001]f(ˆξη) = ˆµη[PDF-GLYPH-U+0002] ∧a ̸= 0. Since α is regular and β < α there is γ < β such that
X = {η < α : ξη = γ} has cardinality α. Then
{[PDF-GLYPH-U+0001]f(ˆγ) = ˆµη[PDF-GLYPH-U+0002] ∧a : η ∈X}
is an antichain of cardinality α > ℵ0 in B, contradicting ccc. (iv) follows.
(v). Assuming the hypotheses, the set {[PDF-GLYPH-U+0001]ξ = ˆη[PDF-GLYPH-U+0002] : η < α} is an antichain in B
and hence the set X = {η < α : [PDF-GLYPH-U+0001]ξ = ˆη[PDF-GLYPH-U+0002] ̸= 0} is countable. Put β = sup X + 1;
then β < α and we have
1 = [PDF-GLYPH-U+0001]ξ < ˆα[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
η<α
[PDF-GLYPH-U+0001]ξ = ˆη[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0006]
η∈X
[PDF-GLYPH-U+0001]ξ = ˆη[PDF-GLYPH-U+0002]
≤
[PDF-GLYPH-U+0004]
η<β
[PDF-GLYPH-U+0001]ξ = ˆη[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]ξ < ˆβ[PDF-GLYPH-U+0002]
and (v) follows.
Finally, we prove a result which will be useful in estimating cardinalities in
V (B). We shall need the notion of ordered pair in V (B): for u, v ∈V (B) we define
{u}(B) = {⟨u, 1⟩}
{u, v}(B) = {u}(B) ∪{v}(B)
⟨u, v⟩(B) = {{u}(B), {u, v}(B)}(B).
It is then easily verified that
V (B) |= ∀x∀y∀u∀v[⟨x, y⟩(B) = ⟨u, v⟩(B) ↔x = u ∧y = v].
Lemma 1.52 For any u ∈V (B) we can find f ∈V (B) such that
V (B) |= Fun(f) ∧dom(f) = dom(u)ˆ ∧u ⊆ran(f)
and hence
V (B) |= |u| ≤|dom(u)ˆ|.
Proof Define
f = {⟨ˆz, z⟩(B): z ∈dom(u)} × {1}.

```

## PDF page 073 | printed page 53

```text
CARDINALS IN V (B)
53
Then it is easily verified that f ∈V (B) meets the required conditions; to
indicate the idea of the proof we show, for example, that [PDF-GLYPH-U+0001]u ⊆ran(f)[PDF-GLYPH-U+0002] = 1.
For we have
[PDF-GLYPH-U+0001]∃x · ⟨x, y⟩∈f[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
x∈V (B)
[PDF-GLYPH-U+0001]⟨x, y⟩∈f[PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0004]
z∈dom(u)
[PDF-GLYPH-U+0001]y = z[PDF-GLYPH-U+0002] ∧
[PDF-GLYPH-U+0004]
x∈V (B)
[PDF-GLYPH-U+0001]x = ˆz[PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0004]
z∈dom(u)
[PDF-GLYPH-U+0001]y = z[PDF-GLYPH-U+0002]
≥
[PDF-GLYPH-U+0004]
z∈dom(u)
u(z) ∧[PDF-GLYPH-U+0001]y = z[PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]y ∈u[PDF-GLYPH-U+0002].
The other conditions are verified similarly.
Note that Lemma 1.52 yields an alternative proof that the axiom of choice
hold in V (B). For, given u ∈V (B), there is by the well-ordering theorem in V an
ordinal α and a bijection g of α onto dom(u). It follows that
V (B) |= ˆg is a bijection of the ordinal ˆα onto dom(u)ˆ.
If f ∈V (B) is as specified in Lemma 1.52, then
V (B) |= f ◦ˆg is a function with domain ˆα and range ⊇u
and so
V (B) |= u is well-orderable.
Since this holds for arbitrary u ∈V (B), V (B) |= AC.
Problem 1.53 (The κ-chain condition) Let κ be an infinite cardinal. B is
said to satisfy the κ-chain condition (κ-cc) if each antichain in B has cardinality
< κ. (Thus the ccc is the ℵ1-cc).
(i) Show that B always satisfies |B|-cc. (If B contains an antichain of
cardinality κ, then 2κ ≤|B|.)
Now assume that B satisfies κ-cc. Show that:
(ii) V (B) |= Card(ˆα) for any cardinal α > κ;

```

## PDF page 074 | printed page 54

```text
54
BOOLEAN-VALUED MODELS OF SET THEORY
(iii) if κ is regular, V (B) |= Card(ˆκ);
(iv) for each X ⊆B there is Y ⊆X such that |Y | < κ and [PDF-GLYPH-U+0003] X = [PDF-GLYPH-U+0003] Y .
(Let A be a maximal antichain in the ideal generated by X; show that
[PDF-GLYPH-U+0003] X = [PDF-GLYPH-U+0003] A. For each a ∈A there is a finite subset Fa ⊆X such that
a ≤[PDF-GLYPH-U+0003] Fa; show that Y = [PDF-GLYPH-U+0015]
a∈A Fa meets the requirements.)

```

## PDF page 075 | printed page 55

```text
2
FORCING AND SOME INDEPENDENCE PROOFS
The forcing relation
Let P = ⟨P, ≤⟩be a fixed but arbitrary partially ordered set. (We shall use
letters p, q, r, p′, q′, r′ to denote elements of P.) Intuitively, the elements of P are
to be thought of as states of information about or conditions on a set-theoretic
state of affairs and the relation p ≤q is to be understood as asserting ‘p refines q’
or ‘the information content of p includes that of q’. Two elements p and q of P
are said to be compatible—written Comp(p, q)—if there is r ∈P such that r ≤p
and r ≤q. The relation Comp(p, q) is intended to express the assertion that
p and q are mutually consistent conditions. P is said to be refined if
∀p, q ∈P[q ≰p →∃p′ ≤q¬Comp(p, p′)].
Thus P is refined if whenever q is not a refinement of p, q has a refinement which
is incompatible with p.
For each p ∈P, put
Op = {q ∈P : q ≤p}.
Then, as is easily verified, the Op form a base for a topology on P called the
(left) order topology. We put RO(P) for the complete Boolean algebra of regular
open sets in this topology.
Let us call a subset X of a Boolean algebra B dense if 0 /∈X and for each
0 ̸= b ∈B there is x ∈X such that x ≤b.
Lemma 2.1
(i) P is refined if and only if Op ∈RO(P) for all p ∈P.
(ii) If P is refined, the map p [PDF-GLYPH-U+0017]→Op is an order-isomorphism of P onto a dense
subset of RO(P).
Proof (i) It is easily verified that, if P is assigned the order topology, then the
interior of the closure of a subset X of P is
(X)◦= {q ∈P : ∀p′ ≤q∃r ∈X[r ≤p′]}.

```

## PDF page 076 | printed page 56

```text
56
FORCING AND SOME INDEPENDENCE PROOFS
Hence
(Op)◦= {q ∈P : ∀p′ ≤q∃r ≤p[r ≤p′]}
= {q ∈P : ∀p′ ≤q Comp(p, p′)}.
(1)
Now suppose that P is refined. We automatically have Op ⊆(Op)◦since
Op is open. Conversely, if q /∈Op, then q ≰p, so since P is refined, there is
p′ ≤q such that ¬Comp(p, p′) and it follows from (1) that q /∈(Op)◦. Therefore
Op = (Op)◦, that is, Op ∈RO(P). Conversely, if Op ∈RO(P), then Op = (Op)◦,
so, using (1), we have q ≰p →q /∈Op →q /∈(Op)◦→∃p′ ≤q¬Comp(p, p′), so
P is refined . This proves (i).
(ii) follows easily from (i) and the definition of the order topology on P.
Corollary 2.2 P is refined iffit is order-isomorphic to a dense subset of a
complete Boolean algebra.
Proof Necessity follows from Lemma 2.1(ii). Conversely, suppose that P is order-
isomorphic to a dense subset of a (complete) Boolean algebra B. Then we may
identify P with a dense subset of B. If p, q ∈P and q ≰p, then (in B) q∧p∗̸= 0,
so since P is dense there is p′ ∈P such that p′ ≤q ∧p∗. Thus p′ ≤q and it is
easy to verify that ¬Comp(p, p′). Therefore P is refined.
Let us say that a pair ⟨B, e⟩(or simply B) is a Boolean completion of P if
the following conditions are met:
(i) B is a complete Boolean algebra;
(ii) e is an order-isomorphism of P onto a dense subset of B.
Lemma 2.3 If ⟨B, e⟩and ⟨B′, e′⟩are Boolean completions of P, then there is
an isomorphism between B and B′ which interchanges e[P] and e′[P].
Proof We give a sketch, leaving the reader to fill in the details. For each x ∈B
put Px = {p ∈P : e(p) ≤x}. Then the density of e[P] in B implies that
x = [PDF-GLYPH-U+0003] e[Px] for each x ∈B. The map f : B →B′ defined for x ∈B by
f(x) = [PDF-GLYPH-U+0003] e′[Px] then meets the requirements.
Corollary 2.2 and Lemma 2.3 imply that each refined partially ordered set P
has a Boolean completion which is unique up to isomorphism.
If P is refined and ⟨B, e⟩is a Boolean completion of P, P will be called a
basis or set of conditions for B (with respect to e). Under these conditions, we
shall frequently identify P with its image e[P] in B, so that P will be regarded
as a dense subset of B.
Remark The notion of the Boolean completion of a partially ordered set is
closely related to the—possibly more familiar—notion of the completion of a
Boolean algebra. A (minimal) completion of a Boolean algebra A is a pair ⟨B, f⟩

```

## PDF page 077 | printed page 57

```text
THE FORCING RELATION
57
in which B is a complete Boolean algebra and f is a complete monomorphism
of A into B such that f[A −{0}] is dense in B.
One easily shows (as in Lemma 2.3) that if ⟨B, f⟩and ⟨B′, f ′⟩are completions
of A, then there is an isomorphism between B and B′, which interchanges f[A]
and f ′[A]. We can obtain the completion ⟨B, f⟩of A in either of the following
two equivalent ways: (1) take ⟨B, e⟩to be a Boolean completion of the partially
ordered set A—{0} and define f : A →B by f(x) = e(x) if x ̸= 0 and f(0) = 0;
(2) take B to be the regular open algebra of the Stone space of A and f the
natural monomorphism of A into B. The completion ⟨B, f⟩of A is characterized
by the following universal property: for any complete Boolean algebra C and any
complete homomorphism g : A →C, there is a unique complete homomorphism
h : B →C such that g = h ◦f.
Problem 2.4 (Boolean completions of nonrefined sets) Let ⟨P, ≤⟩be a
partially ordered set.
(i) Show
that
there
is
a
refined
partially
ordered
set
⟨Q, ⪯⟩
and
an
order
preserving
map
j
of
P
onto
Q
such
that,
for
any,
p, q ∈P, Comp(p, q) ↔Comp(jp, jq). (Define the equivalence relation ∼
on P by p ∼q ↔∀x[Comp(p, x) ↔Comp(q, x)], and take Q = P/ ∼.)
(ii) Show that ⟨Q, ⪯⟩is uniquely determined up to isomorphism.
The partially ordered set Q is called the refined associate of P and the map j
is called the canonical map. If P is refined, we may take Q = P and j to be the
identity.
(iii) Let B be the Boolean completion of Q; then Q may be identified with
a dense subset of B and the canonical map j may be regarded as carrying
P into B. Show that j is an order-preserving map onto a dense subset of B
such that, for p, q ∈P, Comp(p, q) ↔j(p) ∧j(q) ̸= 0.
The algebra B is called the Boolean completion of P.
Now let x and y be nonempty sets, where y has at least two elements. We put
C(x, y) for the set of all mappings with domain a finite subset of x and range a
subset of y. We agree to partially order C(x, y) by ⊇, that is, reverse inclusion,
and it is easy to verify that this turns C(x, y) into a refined partially ordered
set. For p ∈C(x, y) we put
N(p) = {f ∈yx : p ⊆f},
where yx is, as usual, the set of all mappings form x into y. Subsets of yx of
the form N(p) form a base for the product topology on yx, when y is assigned the
discrete topology. Each N(p) is then a clopen (i.e. closed-and-open) set in this
topology. Thus, in particular, each N(p) is a regular open subset of yx, and it is
easy to verify that the map p [PDF-GLYPH-U+0017]→N(p) is an order-isomorphism of C(x, y) onto

```

## PDF page 078 | printed page 58

```text
58
FORCING AND SOME INDEPENDENCE PROOFS
a dense subset of RO(yx). Therefore ⟨RO(yx), N⟩is a Boolean completion of
C(x, y), and the latter is (up to isomorphism) a basis for RO(yx).
Remark In Cohen’s original development of forcing, the ordering of the set of
forcing conditions P ‘goes up’, rather than ‘down’ as we have taken it. In other
words, Cohen holds p ≤q to mean that q contains more information than p. In
particular, the set P = C(x, y) would be taken to be ordered by inclusion and
not, as we have stipulated, by inverse inclusion. This (the ‘more means more’
convention) is of course eminently reasonable, but unfortunately P would then,
in a natural sense, be anti-refined rather than refined, and one could only show
P is order anti-isomorphic to a dense subset (or, equivalently, isomorphic to an
anti-dense subset) of a complete Boolean algebra. (To obtain the ‘anti’-version
of an order-theoretic concept, interchange ‘≤’ and ‘≥’ and ‘0’ and ‘1’.) Since
anti-isomorphisms and anti-dense subsets are not very convenient technically, we
have chosen to reverse the more usual ordering of P and thereby adopt the ‘more
means less’ convention, thus enabling us to use the more familiar machinery of
isomorphisms and dense subsets.
Now let B be a complete Boolean algebra, and let P be a basis for B, with
respect to an order isomorphism e. Identify P with e[P], so that P becomes a
dense subset of B. For each B-sentence σ and each p ∈P we define the relation
p forces σ—written p ⊩σ—by
p ⊩σ iffp ≤[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B.
The basic properties of the forcing relation are contained in the final theorem
of this section. We write [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002] for [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B as usual.
Theorem 2.5 let σ and τ be B-sentence and let φ(x) be a B-formula. Then:
(i) p ⊩¬σ iff¬∃q ≤p[q ⊩σ];
(ii) p ⊩σ ∧τ iffp ⊩σ and p ⊩τ;
(iii) p ⊩σ ∨τ iff∀q ≤p∃r ≤q[r ⊩σ or r ⊩τ];
(iv) p ⊩σ →τ iff∀q ≤p[q ⊩σ →q ⊩τ];
(v) p ⊩∀xφ(x) iff∀u ∈V (B) [p ⊩φ (u)];
(vi) p ⊩∃xφ(x) iff∀q ≤p∃r ≤q∃u ∈V (B) [r ⊩φ(u)];
(vii) for a ∈V, p ⊩∀x ∈ˆaφ(x) iff∀x ∈a[p ⊩φ (ˆx)];
(viii) for a ∈V, p ⊩∃x ∈ˆaφ(x) iff∀q ≤p∃r ≤q∃x ∈a[r ⊩φ(ˆx)];
(ix) [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002] = 0 iff¬∃p[p ⊩σ];
(x) [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002] = 1 iff∀p[p ⊩σ];
(xi) ∀p∃q ≤p[q ⊩σ or q ⊩¬σ];
(xii) [p ⊩σ] →¬[p ⊩¬σ];
(xiii) [q ≤p and p ⊩σ] →q ⊩σ.

```

## PDF page 079 | printed page 59

```text
THE FORCING RELATION
59
Proof We prove some of these assertions, leaving the rest to the reader.
(i) If p ⊩¬σ, then p ≤[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]∗. So in this case if q ≤p, then q ≰[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002] (otherwise
q ≤[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]∗∧[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002] = 0), so ¬[q ⊩σ]. Conversely, if ¬[p ⊩¬σ], then p ≰[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]∗,
so p∧[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002] ̸= 0, so, since P is dense, ∃q ≤p[q ≤[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]], whence ∃q ≤p[q ⊩σ].
(ii)
p ⊩σ ∧τ iffp ≤[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]τ[PDF-GLYPH-U+0002]
iffp ≤[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002] and p ≤[PDF-GLYPH-U+0001]τ[PDF-GLYPH-U+0002]
iffp ⊩σ and p ⊩τ.
(iii)
p ⊩σ ∨τ iffp ⊩¬(¬σ ∧¬τ)
iff¬ ∃q ≤p[q ⊩¬σ ∧¬τ]
iff¬∃q ≤p[q ⊩¬σ and q ⊩¬τ]
iff¬ ∃q ≤p[¬ ∃r ≤q[r ⊩σ] and ¬ ∃r ≤q[r ⊩τ]]
iff∀q ≤p[∃r ≤q[r ⊩σ] or ∃r ≤q[r ⊩τ]]
iff∀q ≤p∃r ≤q[r ⊩σ or r ⊩τ].
(vi)
p ⊩∃xφ(x) iffp ⊩¬ ∀x ¬ φ(x)
iff¬ ∃q ≤p[q ⊩∀x ¬ φ(x)]
iff¬∃q ≤p∀u ∈V (B) ¬∃r ≤q[r ⊩φ(u)]
iff∀q ≤p∃u ∈V (B) ∃r ≤q[r ⊩φ(u)].
(xi) Either p ⊩σ or ¬[p ⊩σ]. If the former, we are finished. If the latter, then
p ≰[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002], so p ∧[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]∗̸= 0, whence ∃q[q ≤p ∧[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]∗], so ∃q ≤p[q ⊩¬σ].
The meaning of Theorem 2.5 can be clarified as follows. We recall that the
elements of p are to be thought of as ‘states of information’, or briefly, ‘states’.
Also, for p, q ∈P, the relation p ≤q means that ‘state’ p is a refinement
(of the information in) ‘state’ q. Then p ⊩σ may be thought of as asserting that
in ‘state’ p we are in definite possession of the ‘fact’ σ, or have been ‘forced’
to accept σ as true. Using this approach, the interpretation of, for example,

```

## PDF page 080 | printed page 60

```text
60
FORCING AND SOME INDEPENDENCE PROOFS
(i) in Theorem 2.5 is:
p ⊩¬σ iffin no state which refines p
will we be forced to accept σ;
that of (vi) is:
p ⊩∃xφ(x) iffany refinement of p can be itself refined
to a state in which we can instantiate φ(x);
and that of (xi) is:
each state can be refined to one in which we either accept σ, or we accept ¬σ.
The reader may provide similar interpretations of the other clauses in
Theorem 2.5.
Finally, we point out that the notion of forcing introduced here is what Cohen
(1966) called weak forcing; Cohen’s original notion of forcing (which we shall
write ⊩c) is customarily known as strong forcing. The two notions are related
by the equivalence
p ⊩σ ↔p ⊩c ¬¬σ.
(∗)
The chief difference between weak and strong forcing is that, while the former
obeys all the laws of classical logic, the latter obeys only the laws of intuitionistic
logic. This means, for example, that if p ⊩σ then p ⊩τ whenever τ is classically
equivalent to σ, while if p ⊩c σ, then one can only infer that p ⊩c τ when τ
satisfies the stronger condition of being intuitionistically equivalent to σ. (Note
in this connection the resemblance between (∗) and the usual translation of
classical into intuitionistic logic.)
Independence of the axiom of constructibility and
the continuum hypothesis
We are now in a position to use the techniques introduced in earlier sections to
prove (among other things) the independence of the axiom of constructibility
and the continuum hypothesis from ZFC.
Theorem 2.6 Let B = RO(2ω). Then:
(i) V (B) |= (Pω)[PDF-GLYPH-U+0001]̸= P ˆω.
(ii) V (B) |= P ˆω ⊈L.

```

## PDF page 081 | printed page 61

```text
AXIOM OF CONSTRUCTIBILITY AND CONTINUUM HYPOTHESIS
61
Proof Put P = C(ω, 2); then B is a completion of P, P is a basis for B, and
each p ∈P is identified with the element
N(p) = {f ∈2ω : p ⊆f}
of B. Define u ∈V (B)by dom(u) = dom(ˆω) and
u(ˆn) = {f ∈2ω : f(n) = 1} ∈B.
It is easy to verify that, for p ∈P and n ∈ω, we have
p ⊩ˆn ∈u iffp(n) = 1;
p ⊩ˆn /∈u iffp(n) = 0.
Also,
[PDF-GLYPH-U+0001]u ∈P ˆω[PDF-GLYPH-U+0002]B = [PDF-GLYPH-U+0001]u ⊆ˆω[PDF-GLYPH-U+0002]B =
[PDF-GLYPH-U+0006]
n∈ω
[u(ˆn) ⇒[PDF-GLYPH-U+0001]ˆn ∈ˆω[PDF-GLYPH-U+0002]B] = 1.
We claim that [PDF-GLYPH-U+0001]u = ˆx[PDF-GLYPH-U+0002]B = 0 for all x ∈Pω. For suppose not; then there
is p ∈P and x ∈Pω such that p ⊩u = ˆx. Pick n ∈ω such that n /∈dom(p).
(Possible, since dom(p) is finite.) If n ∈x, put p′ = p ∪{⟨n, 0⟩}; if n /∈x, put
p′ = p ∪{⟨n, 1⟩}. Then, if n ∈x, we have p′ ⊩ˆn ∈ˆx ∧ˆn /∈u, and if n /∈x, we
have p′ ⊩ˆn /∈ˆx ∧ˆn ∈u. Thus in either case p′ ⊩u ̸= ˆx. But since p′ ≤p, we
have p′ ⊩u = ˆx, which is a contradiction. This establishes the claim.
It follows that
[PDF-GLYPH-U+0001]u ∈(Pω)[PDF-GLYPH-U+0001][PDF-GLYPH-U+0002]B =
[PDF-GLYPH-U+0004]
x∈P ω
[PDF-GLYPH-U+0001]u = ˆx[PDF-GLYPH-U+0002]B = 0,
so
1 = [PDF-GLYPH-U+0001]u ∈P ˆω[PDF-GLYPH-U+0002]B ∧[PDF-GLYPH-U+0001]u /∈(Pω)[PDF-GLYPH-U+0001][PDF-GLYPH-U+0002]B ≤[PDF-GLYPH-U+0001]P ˆω ̸= (Pω)[PDF-GLYPH-U+0001][PDF-GLYPH-U+0002]B
and (i) is proved.
(ii) Consider the set u ∈V (B) defined in the proof of (i). We have, by
Theorem 1.46,
[PDF-GLYPH-U+0001]L(u)[PDF-GLYPH-U+0002]B =
[PDF-GLYPH-U+0004]
x∈L
[PDF-GLYPH-U+0001]u = ˆx[PDF-GLYPH-U+0002]B
=
[PDF-GLYPH-U+0004]
x∈L∩P ω
[PDF-GLYPH-U+0001]u = ˆx[PDF-GLYPH-U+0002]B ∨
[PDF-GLYPH-U+0004]
x∈L−P ω
[PDF-GLYPH-U+0001]u = ˆx[PDF-GLYPH-U+0002]B.

```

## PDF page 082 | printed page 62

```text
62
FORCING AND SOME INDEPENDENCE PROOFS
Since we already know that [PDF-GLYPH-U+0001]u ∈P ˆω[PDF-GLYPH-U+0002]B = 1, we have for x /∈Pω,
[PDF-GLYPH-U+0001]u = ˆx[PDF-GLYPH-U+0002]B = [PDF-GLYPH-U+0001]u = ˆx[PDF-GLYPH-U+0002]B ∧[PDF-GLYPH-U+0001]u ∈P ˆω[PDF-GLYPH-U+0002]B ≤[PDF-GLYPH-U+0001]ˆx ∈P ˆω[PDF-GLYPH-U+0002]B = [PDF-GLYPH-U+0001]ˆx ⊆ˆω[PDF-GLYPH-U+0002]B = 0
since x ⊈ω. Therefore
[PDF-GLYPH-U+0001]L(u)[PDF-GLYPH-U+0002]B =
[PDF-GLYPH-U+0004]
x∈L∩P ω
[PDF-GLYPH-U+0001]u = ˆx[PDF-GLYPH-U+0002]B ≤
[PDF-GLYPH-U+0004]
x∈P ω
[PDF-GLYPH-U+0001]u = ˆx[PDF-GLYPH-U+0002]B = [PDF-GLYPH-U+0001]u ∈(Pω)[PDF-GLYPH-U+0001][PDF-GLYPH-U+0002]B = 0.
Hence [PDF-GLYPH-U+0001]L(u)[PDF-GLYPH-U+0002]B = 0 and (ii) follows immediately.
Recall that in the course of proving Theorem 2.6(i) we remarked that, for
p ∈P = C(ω, 2), we have p ⊩ˆn ∈u iffp(n) = 1, p ⊩ˆn /∈u iffp(n) = 0.
Accordingly, each condition p ∈P may be regarded as encoding a finite ‘piece
of information’ about the members of the ‘new subset’ u of ω. We may therefore
think of C(ω, 2) as the set of conditions for adjoining a new subset of ω using
finite pieces of information, and its completion RO(2ω) as an algebra which
adjoins a new subset of ω.
Theorems 1.19, 1.33, and 2.6 now give:
Corollary 2.7 If ZF is consistent, so is ZFC+ ‘there is a nonconstructible
subset of ω’.
We next show how to extend this result to include the GCH.
Theorem 2.8 Assume the GCH. Then, if B satisfies ccc and |B| = 2ℵ0,
V (B) |= GCH.
Proof Recall from Definition 1.39 that we have, for any u ∈V (B),
dom(P (B)(u)) = Bdom(u)
and
V (B) |= P (B)(u) = Pu.
Take u = ˆℵα. Then since the map x [PDF-GLYPH-U+0017]→ˆx is one–one, we have |dom(ˆℵα)| = ℵα.
Thus, since the GCH is assumed to hold,
|dom(P (B)(ˆℵα))| = |Bdom(ˆℵα) = (2ℵ0)ℵα = 2ℵα = ℵα+1.
It follows from Lemma 1.52 that
V (B) |= |P (B)(ˆℵα)| ≤|ˆℵα+1|.

```

## PDF page 083 | printed page 63

```text
AXIOM OF CONSTRUCTIBILITY AND CONTINUUM HYPOTHESIS
63
But B satisfies ccc, so, by Theorem 1.51, for any α,
V (B) |= ˆℵα = ℵˆα
whence
V (B) |= |ˆℵα+1| = ℵˆα+1.
These two facts give
V (B) |= |P (B)(ℵˆα)| ≤ℵˆα+1,
so that
V (B) |= |Pℵˆα| ≤ℵˆα+1.
Since this holds for arbitrary α, it follows using Problem 1.45 that
V (B) |= ∀α[|Pℵα| ≤ℵα+1]
and so
V (B) |= GCH.
Corollary 2.9 If ZF is consistent, so is ZFC + GCH + ‘there is a noncon-
structible subset of ω’.
Proof Let B be the algebra introduced in Theorem 2.6. Then B statisfies ccc
and |B| = 2ℵ0. Since Consis(ZF) →Consis(ZFC + GCH), the required result
now follows immediately from Theorems 2.6, 2.8, 1.33, and 1.19.
We next turn to the problem of violating the continuum hypothesis in V (B).
The idea here is to make P.
(B)(ˆω) large in V (B); we shall see that this can be
achieved by taking an appropriate B of large cardinality. On the other hand, if
we want to pin down the cardinality of P (B)(ˆω) in V (B), we shall need to make
a reasonably precise estimate of |B|. We now set about doing this for the sort of
B we have in mind.
A topological space X is said to satisfy the countable chain condition (ccc)
if each disjoint family of sets open in X is countable. We have already remarked
that the poduct space 2I satisfies ccc.
Lemma 2.10 Let X be a topological space satisfying ccc. Let E be a base for X
and let B be the regular open algebra of X. Then |B| ≤|E|ℵ0.

```

## PDF page 084 | printed page 64

```text
64
FORCING AND SOME INDEPENDENCE PROOFS
Proof Let U ∈B, and, using Zorn’s lemma, let F be a maximal disjoint subfam-
ily of E ∩PU. Put G = [PDF-GLYPH-U+0015] F. We claim that U = ( ¯G)◦. For since G ⊆U and U is
regular open, we have ( ¯G)◦⊆( ¯U)◦= U. On the other hand, consider U −¯G.
This is an open set; if it is nonempty then it includes a nonempty member of E,
which is disjoint from every member of F, contradicting the maximality of F.
Thus U −¯G = ∅, so that U ⊆¯G and U ⊆( ¯G)◦. This proves the claim.
Accordingly each member of B is determined by a disjoint subfamily of E;
since X satisfies ccc each such subfamily is countable and there are at most |E|ℵ0
of them.
Corollary 2.11 For each set I let 2I be the product space where 2 is assigned
the discrete topology. If |I| = ℵα, then
ℵα ≤|RO(2I)| ≤ℵℵ0
α .
Proof The family of sets of the form
{f ∈2I : f(i1) = a1, . . . , f(in) = an},
where i1, . . . , in ∈I and a1, . . . , an ∈2 is a base for 2I of cardinality ℵα. Since
each set of this form is clopen, it is in RO(2I) and so ℵα ≤|RO(2I)|. On the other
hand, 2I satisfies ccc and so Lemma 2.10 applies to yield the other inequality.
We are now in a position to prove
Theorem 2.12 Suppose that ℵℵ0
α = ℵα and let B = RO(2ω×ωα). Then
V (B) |= 2ℵ0 = ℵˆα.
Proof By Corollary 2.11 we have
ℵα ≤|B| ≤ℵℵ0
α = ℵα,
so that |B| = ℵα. Hence
|dom(P (B)(ˆω))| = |Bdom(ˆω)| = ℵℵ0
α = ℵα
and so, by Lemma 1.52
V (B) |= |P (B)(ˆω)| ≤| ˆ
ℵα|,
whence
V (B) |= |Pω| ≤|ˆℵα|.

```

## PDF page 085 | printed page 65

```text
AXIOM OF CONSTRUCTIBILITY AND CONTINUUM HYPOTHESIS
65
But B satisfies ccc, so by Theorem 1.51 we have V (B) |= |ˆℵα| = ℵˆα, whence
V (B) |= |Pω| ≤ℵˆα,
that is
V (B) |= 2ℵ0 ≤ℵˆα.
It remains to show that
V (B) |= ℵˆα ≤2ℵ0.
To this end, for each ν < ωα define uν ∈V (B) by dom(uν) = dom(ˆω) and
uν(ˆn) = {f ∈2ω×ωα : f(n, ν) = 1}.
We have
[PDF-GLYPH-U+0001]uν ⊆ˆω[PDF-GLYPH-U+0002]B =
[PDF-GLYPH-U+0006]
n∈ω
[uν(ˆn) ⇒[PDF-GLYPH-U+0001]ˆn ∈ˆω[PDF-GLYPH-U+0002]B] = 1.
We also know that P = C(ω × ωα, 2) is a basis for B. Moreover, it is easy to
verify that, for p ∈P,
p ⊩ˆn ∈uν iffp(n, ν) = 1;
p ⊩ˆn /∈uν iffp(n, ν) = 0.
We claim that, if µ, ν < ωα and µ ̸= ν, then [PDF-GLYPH-U+0001]uµ = uν[PDF-GLYPH-U+0002]B = 0. For suppose
not; then there are µ, ν < ωα, µ ̸= ν and p ∈P such that p ⊩uµ = uν. Choose
n ∈ω so that ⟨n, ξ⟩/∈dom(p) for any ξ < ωα (possible, since dom(p) is finite!)
and put
p′ = p ∪{⟨⟨n, µ⟩, 1⟩} ∪{⟨⟨n, ν⟩, 0⟩}.
Then p′ ⊩ˆn ∈uµ ∧ˆn /∈uν, whence p′ ⊩uµ ̸= uν. But since p′ ≤p and
p ⊩uµ = uν, it follows that p′ ⊩uµ = uν. This contradiction proves the claim.
Now define f ∈V (B) by
f = {⟨ˆν, uν⟩(B) : ν < ωα} × {1}.
One then easily verifies (cf. proof of Lemma 1.52) that
V (B) |= f is a map of ˆωα into P ˆω.

```

## PDF page 086 | printed page 66

```text
66
FORCING AND SOME INDEPENDENCE PROOFS
Moreover, since [PDF-GLYPH-U+0001]uµ = uν[PDF-GLYPH-U+0002]B = 0 for µ ̸= ν, it quickly follows that V (B) |= f is
one–one. Since B satisfies the ccc, we have, by Theorem 1.51, V (B) |= ˆωα = ωˆα,
so that
V (B) |= f is a one-one map of ωˆα into P ˆω.
Hence V (B) |= ℵˆα ≤2ℵ0, and we are done.
In the proof of this last theorem we remarked that, for p ∈P = C(ω ×ωα, 2),
we have p ⊩ˆn ∈uν iffp(n, ν) = 1; p ⊩ˆn ∈uν iffp(n, ν) = 0. Thus each condition
p ∈P may be thought of as encoding a finite ‘piece of information’ about the
members of the ℵα ‘new subsets’ uν of ω. We may therefore regard C(ω × ωα, 2)
as the set of conditions for adjoining ℵα new subsets of ω using finite pieces of
information, and its completion RO(2ω×ωα) as an algebra which adjoins ℵα new
subsets of ω.
Corollary 2.13 If ZF is consistent, so is ZFC + 2ℵ0 = ℵ2.
Proof In ZFC + GCH we have ℵℵ0
2
= (2ℵ1)ℵ0 = 2ℵ1 = ℵ2, so by Theorem 2.12
one can prove in ZFC + GCH the existence of a complete Boolean algebra B
such that V (B) ⊨2ℵ0 = ℵ2. Since Consis(ZF) →Consis(ZFC + GCH), the
required result now follows from Theorems 1.33 and 1.19.
Similar arguments show that in Corollary 2.13 ‘ℵ2’ can be replaced by ‘ℵ3’,
‘ℵω+1’, ‘ℵω1’, etc.
Problems
Throughout, κ denotes an infinite cardinal and B a complete Boolean algebra.
In Problems 2.14, 2.15, and 2.16, for any cardinal λ, λκ, and ˆλˆκ are understood
to denote, respectively, the set of all maps of κ into λ, and ‘the set of all maps
of ˆκ into ˆλ in V (B).
2.14 (Infinite distributive laws and V (B)) Let λ be a cardinal (finite or
infinite). B is said to be (κ, λ)-distributive if for any double sequence {bαβ :
⟨α, β⟩∈κ × λ} ⊆B we have
[PDF-GLYPH-U+0006]
α<κ
[PDF-GLYPH-U+0004]
β<λ
bαβ =
[PDF-GLYPH-U+0004]
f∈λκ
[PDF-GLYPH-U+0006]
α<κ
bαf(α).
Show that the following conditions are equivalent:
(i) B is (κ, λ)-distributive;
(ii) V (B) |= ˆλˆκ = (λκ)ˆ.

```

## PDF page 087 | printed page 67

```text
AXIOM OF CONSTRUCTIBILITY AND CONTINUUM HYPOTHESIS
67
(Use the fact that
[PDF-GLYPH-U+0001]h ∈ˆλˆκ[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0006]
α<κ
[PDF-GLYPH-U+0004]
β<λ
bαβ and [PDF-GLYPH-U+0001]h ∈(λκ)ˆ[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
f∈λκ
[PDF-GLYPH-U+0006]
α<κ
bαf(α),
where bαβ = [PDF-GLYPH-U+0001]h(ˆα) = ˆβ[PDF-GLYPH-U+0002].)
2.15 (Infinite distributive laws and V (B) continued)
(i) B is said to satisfy the restricted (κ, 2)-distributive law if for each double
sequence {bαn : ⟨α, n⟩∈κ × 2} ⊆B such that bα0 = b∗
α1 for all α < κ, we
have [PDF-GLYPH-U+0003]
f∈2κ
[PDF-GLYPH-U+0002]
α<κ bαf(α) = 1.
Show that the following conditions are equivalent:
(a) B satisfies the restricted (κ, 2)-distributive law;
(b) B is (κ, 2)-distributive;
(c) B is (κ, κ)-distributive;
(d) B is (κ, 2κ)-distributive;
(e) V (B) ⊨ˆκˆκ = (κκ)[PDF-GLYPH-U+0001];
(f) V (B) ⊨P ˆκ = (Pκ)[PDF-GLYPH-U+0001].
(Show that (a) →(f) →(e) →(d) →(c) →(b) →(a). For (a) →(f),
use (a) to prove V (B) ⊨u ∈(Pκ)ˆ for any u ∈Bdom(ˆκ). For (f) →(e),
use the fact that κκ ⊆2κ×κ and |κ| = |κ × κ|. For (e) →(d), observe
that (2κ)κ = 2κ×κ and use Theorem 2.12. The remaining implications are
trivial.)
(ii) Show that RO(2ω) is not (ω, 2)-distributive. (Use (i) and Theorem 2.6(i).)
2.16 (Weak distributive laws and V (B)) B is said to be weakly (ω, κ)-
distributive if for each double sequence {bnα : ⟨n, α⟩∈ω × κ} we have
[PDF-GLYPH-U+0006]
n∈ω
[PDF-GLYPH-U+0004]
α<κ
bnα =
[PDF-GLYPH-U+0004]
f∈κω
[PDF-GLYPH-U+0006]
n∈ω
[PDF-GLYPH-U+0004]
α≤f(n)
bnα.
Clearly, if B is (ω, κ)-distributive, B is weakly (w, κ)-distributive. (But the
converse fails: for example, if B is the complete Boolean algebra of Lebesgue
measurable subsets of [0,1] modulo the ideal of sets of measure 0, then it can be
shown that B is weakly (ω, ω)-distributive but not (ω, ω)-distributive.)
We define the cofinality cf(κ) of κ to be the least ordinal which is the order
type of a cofinal subsct of κ. Thus cf (κ) > ω iff∀f ∈κω∃β < κ∀n ∈ω[f(n) ≤β],
that is, iffeach function from ω to κ is bounded by some ordinal < κ.
(i) Show that, if cf (κ) > ω, then
[PDF-GLYPH-U+0004]
f∈κω
[PDF-GLYPH-U+0006]
n∈ω
[PDF-GLYPH-U+0004]
α≤f(n)
bnα =
[PDF-GLYPH-U+0004]
β<κ
[PDF-GLYPH-U+0006]
n∈ω
[PDF-GLYPH-U+0004]
α≤β
bnα.

```

## PDF page 088 | printed page 68

```text
68
FORCING AND SOME INDEPENDENCE PROOFS
(ii) Show that,
if B satisfies ccc and cf (κ)
>
ω,
then B is weakly
(ω, κ)-distributive. (Let {bnα : ⟨n, α⟩∈ω × κ} ⊆B. Using Prob-
lem 1.53(iv), replace each {bnα : α < κ} by a countable subset Cn having
the same supremum.)
(iii) Suppose that cf (κ) > ω. Show that B is weakly (ω, κ)-distributive
iffV (B) |= (cf κ)ˆ
> ˆω. (Note that [PDF-GLYPH-U+0001]f ∈ˆκˆω[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0002]
n∈ω
[PDF-GLYPH-U+0003]
α<κ bnα
and that [PDF-GLYPH-U+0001]∃β < ˆκ∀n ∈ˆω[f(n) ≤β][PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0003]
β<κ
[PDF-GLYPH-U+0002]
n∈ω
[PDF-GLYPH-U+0003]
α≤β bnα, where
bnα = [PDF-GLYPH-U+0001]f(ˆn) = ˆα[PDF-GLYPH-U+0002].)
(iv) Show that B is weakly (ω, ω)-distributive iffV (B) |= ∀g[g ∈ˆωˆω →∃f ∈
(ωω)ˆ∀n ∈ˆω[g(n) ≤f(n)], in other words; iffin V (B) the standard numer-
ical functions are cofinal in the class of all numerical functions. (Argue as
in (iii).)
2.17 (κ-closure
and V (B)) Let P
be a basis for B.
P
is said to
be κ-closed if for each ordinal α
<
κ and each descending α-sequence
p0 ≥p1 ≥· · · ≥pβ ≥· · · (β < α) in P there is p ∈P such that p ≤pβ for all
β < α. Consider the following conditions:
(i) B has a dense subset P which is κ-closed;
(ii) for any α < κ and any x ∈V ,
V (B) |= ˆxˆα = (xα)[PDF-GLYPH-U+0001];
(iii) V (B) |= Card(ˆα) for any cardinal α ≤κ;
(iv) V (B) |= P ˆα = (Pα)[PDF-GLYPH-U+0001] for any α ≤κ.
Show that (i) →(ii) →(iii), and (ii) →(iv). Hence (i) implies that B is
(α, λ)-distributive for any α < κ and any λ. (For (i) →(ii), let p ∈P be such
that p ⊩f ∈ˆxˆα. Using (i), find a descending sequence {pβ : β < α} ⊆P and a
set {yβ : β < α} ⊆x such that pβ ⊩f(ˆβ) = ˆyβ. If q ∈P satisfies q ≤pβ for all
β < α, and g = {⟨β, yβ⟩: β < α}, show that q ⊩f = ˆg.)
2.18 (An important set of conditions) Let x and y be nonempty sets,
where |y| ≥2. We put Cκ(x, y) for the set—partially ordered by ⊇—of all
maps with domain a subset of x of cardinality < κ and range a subset of y. Put
Bκ(x, y) for the regular open algebra of the space yx with the topology whose
basic open sets are of the form
N(p) = {f ∈yx : p ⊆f}
for p ∈Cκ(x, y). Observe that Cω(x, y) = C(x, y).
(i) Show that Cκ(x, y) is refined,
and that ⟨Bκ(x, y), N⟩is a Boolean
completion of Cκ(x, y). Thus Cκ(x, y) is an basis for Bκ(x, y).
(ii) Show that, if κ is regular, Cκ(x, y) is κ-closed.

```

## PDF page 089 | printed page 69

```text
AXIOM OF CONSTRUCTIBILITY AND CONTINUUM HYPOTHESIS
69
(iii) Assume GCH, κ is regular and |y| ≤κ. Show that, if I is any set of pairwise
incompatible elements of Cκ(x, y), then |I| ≤κ. (Fix a well-ordering of I.
Define a sequence {xα : α < κ+} of subsets of x by: x0 = ∅; xα = [PDF-GLYPH-U+0015]
β<α xβ
for limit α, xα+1 = xα ∪[PDF-GLYPH-U+0015]{dom(q) : for some p ∈Cκ(xα, y), q is the least
element of I such that q|xα = p}. Show that |xα| ≤κ for α < κ+, and
hence that |Cκ(xκ, y)| ≤κ. Now prove that I ⊆Cκ(xκ, y): for any p ∈I,
Show that there is α < κ such that dom(p) ∩xα = dom(p) ∩xα+1; choose
q ∈I such that p|xα = q|xα and dom(q) ⊆xα+1; show that p and q
coincide on dom(p) ∩dom(q); deduce that p = q and p ∈Cκ(xκ, y).)
(iv) Assume GCH, κ is regular and |y| ≤κ. Show that Bκ(x, y) satisfies κ+−cc.
(Use (iii).)
(v) Assume GCH, κ and |x| are regular and κ < |x|. Show that |Bκ(x, 2)| = |x|.
(Using (iii), argue as in Lemma 2.10.)
2.19 (Consistency of 2ℵ0 = ℵ2 + ∀κ ≥ℵ1[2κ = κ+] with ZFC)
(i) Show that, if |B| = λ, then V (B) |= |P ˆκ| ≤|(λκ)ˆ|. (Use Lemma 1.52.)
(ii)1 Assume GCH, and let |B| = λ ≥ℵ0. Show that V (B) |= ∀α ≥ˆλ[Card(α) →
2α = α+]. Use Problem 1.53 and (i).)
(iii) Assume GCH, and let B = RO(2ω×ω2). Show that V (B) |= 2ℵ1 = ℵ2
(Use (i)) and deduce from this, Theorem 2.12 and (ii) that if ZF is
consistent, so is ZFC + 2ℵ0 = ℵ2 + ∀κ ≥ℵ1[2κ = κ+].
2.20 (A further relative consistency result) Assume GCH. Let κ, λ be
regular cardinals such that κ < λ. Put B = Bκ(κ × λ, 2) (Problem 2.18).
(i) Show that V (B) |= Card(ˆα) for any cardinal α. (For α ≤κ, use
Problems 2.18(ii) and 2.17(iii). For α ≥κ+, use Problems 2.18(iv)
and 1.53).
(ii) Show that V (B)
|= P ˆα = (Pα)ˆ for any cardinal α < κ. (Use
Problems 2.18(ii) and 2.17(iv).)
(iii) Show that
V (B) |= ∀α < ˆκ[Card(α) ∧ℵ0 ≤α →2α = α+].
(Use (i), (ii), and GCH.)
(iv) Show that
V (B) |= ∀α ≥ˆλ[Card(α) →2α = α+].
(Use Problems 2.18(v), 2.19(i), and (i).)
1This result shows that, as long as B is a set (i.e. has a cardinality ) we cannot provably
violate the GCH in V (B) at arbitrarily high cardinals. It turns out, however, that this can be
achieved when B is a suitably chosen (proper) class. The details are, unfortunately, too lengthy
to be included here. See Easton (1970), Takeuti and Zaring (1973), or Shoenfield (1971).

```

## PDF page 090 | printed page 70

```text
70
FORCING AND SOME INDEPENDENCE PROOFS
(v) Show that
V (B) |= ∀α[Card(α) ∧ˆκ ≤α < ˆλ →2α = ˆλ].
(Use Problems 2.18(iv) and 2.19(i) to show that V (B) |= 2ˆα ≤ˆλ for κ ≤
α < λ and argue as in the proof of Theorem 2.12 to get V (B) |= 2ˆκ ≥ˆλ.)
(vi) Deduce that, if ZF is consistent, so is
ZFC + 2ℵ0 = ℵ1 + ∀κ[ℵ1 ≤κ ≤ℵω →2κ = ℵω+1]
+ ∀κ[ℵω+1 ≤κ →2κ = κ+].
2.21 (Consistency of GCH + Pω ⊆L + Pω1 ⊈L with ZFC) Assume GCH,
let κ be regular, and put B = Bκ(κ, 2).
(i) Show that V (B) |= Card(ˆα) for any cardinal α. (Like Problem 2.20(i).)
(ii) Show that V (B)
|= P ˆα = (Pα)ˆ for any cardinal α < κ. (Like
Problem 2.20(ii).)
(iii) Show that V (B) |= P ˆκ ̸= (Pκ)ˆ. (Like Theorem 2.6(i).)
(iv) Show that V (B) |= GCH. (To show V (B) |= 2ˆα = ˆα+ for α < κ, argue as
in Problem 2.20(iii). (To show V (B) |= 2ˆα = ˆα+ for α ≥κ, argue as in
Problem 2.20(iv).)
(v) Assume V = L. Show that
V (B) |= ∀α < ˆκ[Pα ⊆L] ∧P ˆκ ⊈L.
(Using (i) and (ii), argue as in Theorem 2.6.)
(vi) Deduce that, if ZF is consistent, so is ZFC + GCH + Pω ⊆L + Pω1 ⊈L.

```

## PDF page 091 | printed page 71

```text
3
GROUP ACTIONS ON V (B) AND THE INDEPENDENCE
OF THE AXIOM OF CHOICE
Group actions on V (B)
Let G be a group, and X a class. An action of G on X is a map ⟨g, x⟩[PDF-GLYPH-U+0017]→g · x :
G × X →X satisfying
1 · x = x
and
(gh) · x = g · (h · x)
for all x ∈X, g, h ∈G, where 1 is the identity element of G. (When confusion is
unlikely, we write gx for g · x.) Under these conditions we say that G acts on X.
For each g ∈G, the map πg : X →X defined by πg(x) = g · x is a permutation
of X, and the correspondence g [PDF-GLYPH-U+0017]→πg defines a homomorphism of G into the
group of permutations of X.
If B is a Boolean algebra, by an action of a group G on B we shall always mean
an action of G by automorphisms, that is, one in which each πg as defined above
is not merely a permutation but actually an automorphism of B. In particular,
the automorphism group Aut(B) of B acts on B in the natural way via:
π · b = π(b)
for π ∈Aut(B), b ∈B.
We can extend the notion of group actions to Boolean-valued structures as
follows. Let B be a complete Boolean algebra, and let S = ⟨S, [[· = ·]]S, [[· ∈·]]S⟩
be a B-valued structure. An action of a group G on S is a pair of actions of G
on B and the class S satisfying
[[gu = gv]]S = g · [[u = v]]S
[[gu ∈gv]]S = g · [[u ∈v]]S.
(3.1)
It is easily shown by induction on the complexity of formulas that for any formula
φ(v1, . . . , vn) of L, any x1, . . . , xn ∈S and any g ∈G,
[[φ(gx1, . . . , gxn)]]S = g · [[φ(x1, . . . , xn)]]S.
(3.2)
We now show that any action of a group G on a complete Boolean algebra
B extends naturally to an action of G on the B-valued structure V (B).

```

## PDF page 092 | printed page 72

```text
72
GROUP ACTIONS AND INDEPENDENCE OF AC
Theorem 3.3 Let G be a group acting on the complete Boolean algebra B.
Define the map ⟨g, u⟩[PDF-GLYPH-U+0017]→gu : G × V (B) →V (B) by recursion on the well-founded
relation y ∈dom(x) via
gx = {⟨gx, g · u(x)⟩: x ∈dom(u)}.
(3.4)
Then this defines an action of G on V (B) such that :
(i) for any u ∈V (B), g ∈G, we have dom(gu) = {gx : x ∈dom(u)} and, for
any x ∈dom(u), (gu)(gx) = g · u(x);
(ii) gˆv = ˆv for any v ∈V .
Proof To show that (3.4) defines an action of G on V (B), we first prove that for
any g ∈G the map x [PDF-GLYPH-U+0017]→gx for x ∈V (B) is one–one and sends V (B) into itself.
For this it suffices to show by induction on α that
(1) the restriction to V (B)
α
of x [PDF-GLYPH-U+0017]→gx is one–one from V (B)
α
to V (B).
Assume that (1) holds for all β < α. If u ∈V (B)
α
then dom(u) ⊆V (B)
β
for
some β < α, so that the restriction of x [PDF-GLYPH-U+0017]→gx to dom(u) is a one–one map of
dom(u) into V (B). It follows immediately that gu as defined by (3.4) is a map
of {gx : x ∈dom(u)} ⊆V (B) into B, so that gu ∈V (B). Thus the restriction
to V (B)
α
of x [PDF-GLYPH-U+0017]→gx carries V (B)
α
into V (B). To show that it is one–one, suppose
that u, v ∈V (B)
α
and gu = gv. Then, by (3.4),
(2) {⟨gx, g · u(x)⟩: x ∈dom(u)} = {⟨gy, g · v(y)⟩: y ∈dom(v)}.
But there is β < α such that V (B)
β
includes both dom(u) and dom(v), so that
x [PDF-GLYPH-U+0017]→gx is one–one on both these sets. It now follows from (2) that
{⟨x, u(x)⟩: x ∈dom(u)} = {⟨y, v(y)⟩: y ∈dom(v)}
that is, u = v. Hence the restriction to V (B)
α
of x [PDF-GLYPH-U+0017]→g · x is one–one and (1)
is proved.
Part (i) now follows immediately from (3.4).
To establish that ⟨g, u⟩[PDF-GLYPH-U+0017]→gu is an action of G on V (B), we first use the
induction principle for V (B) to show that (gh)u = g(hu) for any g, h ∈G, u ∈
V (B). Assuming accordingly that (gh)x = g(hx) for all x ∈dom(u), we compute
g(hu) = {⟨gy, g(hu)(y)⟩: y ∈dom(hu)}
= {⟨g(hx), g(hu)(hx)⟩: x ∈dom(u)}
= {⟨g(hx), g(h · u(x))⟩: x ∈dom(u)}
= {⟨(gh)x, (gh) · u(x)⟩: x ∈dom(u)}
= (gh)u,

```

## PDF page 093 | printed page 73

```text
GROUP ACTIONS ON V (B)
73
which proves the assertion. Similarly, one shows that 1u = u for all u ∈V (B).
The facts that
g · [[u ∈v]] = [[gu ∈gv]]
and
g · [[u = v]] = [[gu = gv]]
are proved simultaneously using the induction principle for V (B). We omit the
straightforward details.
Finally (ii) is proved by a simple induction on the well-founded relation y ∈x.
Recall that the automorphism group Aut(B) of B acts on B; hence it also
acts on V (B). An element x of B or of V (B) is said to be invariant if πx = x
for every π ∈Aut(B). B is said to be homogeneous if 0 and 1 are its only
invariant elements.
Problem 3.5 (Another characterization of homogeneity) Show that B
is homogeneous ifffor each x ̸= 0, y ̸= 0 in B there is an automorphism π of B
such that x ∧πy ̸= 0. (Consider [PDF-GLYPH-U+0003] {πy : π an automorphism of B}.)
Next we show that homogeneity of B confers certain desirable properties
on V (B).
Lemma
3.6 Suppose
that
B
is
homogeneous.
Then,
for
any
formula
φ(v1, . . . , vn) and any x1, . . . , xn ∈V , either [[φ(ˆx1, . . . , ˆxn)]]B = 0 or else
[[φ(ˆx1, . . . , ˆxn)]]B = 1. In particular, for any sentence σ, either [[σ]]B = 0 or
[[σ]]B = 1.
Proof By (3.2) and Theorem 3.3(ii) [[φ(ˆx1, . . . , ˆxn)]]B is an invariant element of
B. The result now follows from the homogeneity of B.
To conclude this section, we establish the existence of a large class of
homogeneous algebras.
Lemma 3.7 For any set I, RO(2I) is homogeneous.
Proof For each i ∈I define πi : 2I →2I by πif = f i for f ∈2I, where f i ∈2I
is defined by
f i(j) = f(j) for j ̸= i
f i(i) = 1 −f(i).

```

## PDF page 094 | printed page 74

```text
74
GROUP ACTIONS AND INDEPENDENCE OF AC
It is easy to check that πi is a homeomorphism of 2I onto itself, and so induces
an automorphism π′
i of RO(2I) = B defined by
π′
i(U) = π−1
i
[U]
for U ∈B.
Suppose now that U is an invariant element of B. Then if U ̸= ∅there is a
basic open set
n
[PDF-GLYPH-U+0007]
k=1
{f ∈2I : f(ik) = ak} ⊆U,
(1)
where {i1, . . . , in} ⊆I and {a1, . . . , an} ⊆2. Applying π′
in and using the
invariance of U, it follows that
n−1
[PDF-GLYPH-U+0007]
k=1
{f ∈2I : f(ik) = ak} ∩{f ∈2I : f(in) = 1 −an} ⊆U.
This, together with (1) implies
n−1
[PDF-GLYPH-U+0007]
k=1
{f ∈2I : f(ik) = ak} ⊆U.
Continuing in this way we get 2I ⊆U, so that U = 1 in B. The homogeneity of
B follows.
The independence of the existence of definable
well-orderings of P ω
We now apply the results of the previous section to show that, if ZF is consistent,
so is ZFC + GCH + ‘there is no definable well-ordering of Pω’. Thus, although
in ZFC one can prove the existence of a well-ordering of Pω, even in the presence
of GCH it is consistent to assume that no such well-ordering can be explicitly
defined.
For each formula φ(x, y) let WOφ be the sentence ‘φ defines a well-ordering
of Pω’. Then we have
Theorem 3.8 Let B = RO(2ω). Then for any formula φ(x, y) we have
V (B) |= ¬WOφ.
Proof Before launching into formalities we give an outline of the proof. By
Theorem 2.6 P ˆω−(Pω)[PDF-GLYPH-U+0001] is nonempty in V (B). If P ˆω had a definable well-ordering

```

## PDF page 095 | printed page 75

```text
EXISTENCE OF DEFINABLE WELL-ORDERINGS OF Pω
75
in V (B), P ˆω −(Pω)[PDF-GLYPH-U+0001] would have a definable least element u. But then u would
be invariant, and one can use the homogeneity of B to show that u ∈(Pω)[PDF-GLYPH-U+0001] in
V (B), a contradiction.
Now for the formal details. Put c = [[WOφ]]B and write S for P ˆω −(Pω)[PDF-GLYPH-U+0001] in
V (B). Then, by Lemmas 3.7 and 3.6, either c = 0 or c = 1; we have to prove the
former. Suppose, for contradiction’s sake, that c = 1. By Theorem 2.6 we have
V (B) |= S ̸= ∅, so it follows that
(1) V (B) |= ∃!x ∈S∀y ∈Sφ(x, y).
Hence, by the Maximum Principle, there is u ∈V (B) such that
(2) V (B) |= u ∈S ∧∀y ∈Sφ(u, y).
We have V (B) |= u ⊆ˆω and, by (1) and (2), for all n ∈ω,
V (B) |= [ˆn ∈u ↔∃x ∈S[ˆn ∈x ∧∀y ∈Sφ(x, y)]].
Hence
[[ˆn ∈u]]B = [[∃x ∈S[ˆn ∈x ∧∀y ∈Sφ(x, y)]]]B.
Now the r.h.s. of this equation is evidently invariant, so by Lemmas 3.6 and 3.7
the l.h.s. is either 0 or 1. Put
v = {n ∈ω : [[ˆn ∈u]]B = 1}.
Then [[ˆn ∈ˆv]]B = [[ˆn ∈u]]B, so that
[[∀x ∈ˆw[x ∈u ↔x ∈ˆv]]]B = 1,
Whence V (B) |= u = ˆv, and thus V (B) |= u ∈(Pω)[PDF-GLYPH-U+0001]. But this contradicts the
fact—immediate from (2)—that V (B) |= u /∈(Pω)[PDF-GLYPH-U+0001]. Thus c = 0 and we are
through.
Corollary 3.9 If ZF is consistent, so is
ZFC + GCH + {¬WOφ : φ(x, y) a formula}.
Proof If B = RO(2ω) then |B| = 2ℵ0 and so by 2.8 in ZFC + GCH we can prove
that V (B) |= GCH. The required result now follows easily from this, Lemma 3.7,
Theorems 3.8, 1.33, and 1.19.
Problems
3.10 (The Boolean-valued subset defined by a formula) Let ψ(x) be any
B-formula and let u ∈V (B). Recall that in the proof of Lemma 1.35 we showed
that the object v ∈V (B) defined by dom(v) = dom(u) and v(x) = u(x) ∧[[ψ(x)]]

```

## PDF page 096 | printed page 76

```text
76
GROUP ACTIONS AND INDEPENDENCE OF AC
for x ∈dom(v) satisfies V (B) |= ∀x[x ∈v ↔x ∈u ∧ψ(x)]. Write v = {x ∈u :
ψ(x)}(B). Now suppose that B is homogeneous, φ(x, v1, . . . , vn) is any formula
and a, a1, . . . , an ∈V . Show that
V (B) |= {x ∈ˆa : φ(x, ˆa1, . . . , ˆan)}(B) ∈(Pa)[PDF-GLYPH-U+0001].
3.11 (Ordinal definable sets in V (B)) We recall (cf. Drake 1974, ch. 5) that a
set u is said to be ordinal definable—written OD(u)—if for some formula φ and
ordinals α1, . . . , αn, u is the unique set such that φ(u, α1, . . . , αn) holds. The set
u is hereditarily ordinal definable—written HOD(u)—if all the members of the
transitive closure of {u} are ordinal definable. We put OD = {u : OD(u)} and
HOD = {u : HOD(u)}. Recall the following facts:
(a) OD has a definable well-ordering and, for any set u, u ⊆OD iffu has a
definable well-ordering;
(b) L ⊆HOD ⊆OD.
(i) Show that L = HOD ifffor all u, (u ⊆L ∧u ∈OD) →u ∈L. (Use
∈-induction.)
(ii) Suppose that B is homogeneous. Show that V = L →V (B) |= L =
HOD. (Use (i) and Problem 3.10.)
(iii) Show that, if ZF is consistent, so is ZFC+GCH+L = HOD+HOD ̸=
V . (Use (ii) and Corollary 3.9.)
3.12 (Complete homomorphisms) Let B and B′ be complete Boolean algeb-
ras. Recall that a homomorphism h : B →B′ is said to be complete if
h([PDF-GLYPH-U+0003] X) = [PDF-GLYPH-U+0003] h[X] for any X ⊆B.
(i) Let h be a complete monomorphism of B into B′. Define the map ¯h on
V (B) by recursion: for all u ∈V (B)
¯hu = {⟨¯hx, h(u(x))⟩: x ∈dom(u)}.
Show that h is an injection of V (B) into V (B′) such that, for any u, v ∈
V (B), h[[u ∈v]]B′ = [[¯hu ∈¯hv]]B′, h[[u = v]]B = [[¯hu = ¯hv]]B and, for
x ∈V, ¯hˆx = ˆx. (Argue inductively as in the proof of Theorem 3.3.)
Throughout the remainder of this problem take h to be a complete
homomorphism of B into B′.
(ii) Define the map ˜h on V (B) by recursion: for u ∈V (B)
˜hu =
[PDF-GLYPH-U+0018][PDF-GLYPH-U+0019]
˜hx,
[PDF-GLYPH-U+0004]
B′
{h(u(y)) : y ∈dom(u) ∧˜hx = ˜hy}
[PDF-GLYPH-U+001A]
: x ∈dom(u)
[PDF-GLYPH-U+001B]
.

```

## PDF page 097 | printed page 77

```text
EXISTENCE OF DEFINABLE WELL-ORDERINGS OF Pω
77
Show that (a) ˜h : V (B) →V (B′), (b) ˜h is onto if h is, (c) ˜h = ¯h if h
is a monomorphism, (d) ˜hˆx = ˆx for x ∈V , (e) h[[u ∈v]]B = [[˜hu = ˜hv]]B′,
h[[u = v]]B = [[˜hu = ˜hv]]B′ for u, v ∈V (B). (Argue inductively.)
(iii) If h′ is a complete homomorphism of B′ into a complete Boolean algebra
B′′, show that (h′ ◦h)[PDF-GLYPH-U+0002]= ˜h′ ◦˜h. (Argue inductively.)
(iv) Show that for any Σ1-formula φ(v1, . . . , vn) and any x1, . . . , xn ∈V (B)
h[[φ(x1, . . . , xn)]]B ≤[[φ(˜hx1, . . . , ˜hxn)]]B′.
(v) Show that, if h is onto, then for any formula φ(v1, . . . , vn) and any
x1, . . . , xn ∈V (B),
h[[φ(x1, . . . , xn)]](B) = [[φ(˜hx1, . . . , ˜hxn)]]B′.
3.13 (Ultrapowers as Boolean extensions)
(i) Let I be a set and for each i ∈I define φi : PI →2 by πi(X) = 1 if
i ∈X, πi(X) = 0 if i /∈X; then πi is a complete homomorphism of the
complete Boolean algebra PI onto 2. Let φ(v1, . . . , vn) be a formula and
let x1, . . . , xn ∈V (P I). Show that
[[φ(x1, . . . , xn)]]P I = {i ∈I : [[φ(˜πix1, . . . , ˜πixn)]]2 = 1}.
(Use Problem 3.12(v).)
(ii) Let B be a complete Boolean algebra and let U be an ultrafilter in B.
Define the relation ∼U on V (B) by x ∼U y ↔[[x = y]] ∈U; then ∼U is
an equivalence relation on V (B). For each x ∈V (B) let xU = {y ∈V (B) :
x ∼U y} be the ∼U-equivalence class of x. Define the relation ∈U on the
class1 {xU : x ∈V (B)} by xU ∈U yU ↔[[x ∈y]] ∈U. Let V (B)/U be the
structure ⟨{xU : x ∈V (B)}, ∈U⟩: this is called the quotient of V (B) by U.
(For a fuller treatment of quotients, see Chapter 4.) Let φ(v1, . . . , vn) be
a formula and let x1, . . . , xn ∈V (B). Show that
V (B)/U |= φ[xU
1 , . . . , xU
n ] iff[[φ(x1, . . . , xn)]] ∈U.
(Induction on the complexity of φ, using the Maximum Principle to handle
the existential case.)
(iii) Let I be a set. Define g : V (2) →V by putting, for each u ∈V (2), g(u) =
the unique x ∈V such that V (P I) |= u = ˆx (Theorem 1.23(iv)). Define h :
V (P I) →V I, the set of all maps with domain I, by h(x) = {g(˜πix) : i ∈I}
1Strictly speaking, each xU is itself a (proper) class, so {xU : x ∈V (B)} is not defined.
However, this annoyance can be overcome by Scott’s well-known trick of replacing each xU by
the set of its members of minimum rank.

```

## PDF page 098 | printed page 78

```text
78
GROUP ACTIONS AND INDEPENDENCE OF AC
for x ∈V (P I). Show that h is onto. (Start with f ∈V I; observe that
{f −1(f(i)) : i ∈I} is a partition of unity in PI. Hence by Problem 1.26(i)
there is x ∈V (P I) such that [[x = f(i)[PDF-GLYPH-U+0001]]]P I = f −1(f(i)) for i ∈I. Show,
using Problem 3.12 and (i), that h(x) = f.)
(iv) Let I be a set, let U be an ultrafilter in PI, and let V I/U be the usual
ultrapower of V by U. Define j : V (P I)/U →V I/U by j(xU) = h(x)/U,
the canonical image of h(x) in V I/U (and h is defined as in (iii)). Show
that j is an isomorphism of V (P I)/U onto V I/U. (Use (i), (ii), and (iii).)
Thus, each ultrapower of V can be obtained as a quotient of a suitable
Boolean extension of V .
The independence of the axiom of choice
We turn next to the problem of establishing the relative consistency of ¬AC
with ZF. Now it is clear that we cannot do this by trying to falsify AC in some
V (B) (as, for example, we did with CH), because we know that in ZFC one can
prove that AC is true in V (B). It turns out, however, that, if B is acted on by
a suitable group, then we can falsify AC in certain submodels of V (B). We first
give a heuristic sketch of the argument.
Let G be the group of all permutations of ω and for each n ∈ω let
Gn = {g ∈G : gn = n}.
We choose a certain complete Boolean algebra B and construct a certain subclass
V (Γ) of V (B) such that
(i) V (Γ) is a B-valued model of ZF such that ˆx ∈V (Γ) for all x ∈V ;
(ii) G acts on V (Γ);
(iii) for each x ∈V (Γ), there is a finite subset J ⊆ω (called a support of x)
such that gx = x for every g ∈[PDF-GLYPH-U+001C]
n∈J Gn;
(iv) there is an infinite ‘set of distinct reals’ {un : n ∈ω} = s in V (Γ) such that
gun = ugn for all g ∈G.
Then, in V (Γ), s is infinite but not Dedekind infinite, so a fortiori the axiom
of choice fails in V (Γ). For suppose f is any map in V (Γ) of ˆω into s. Then, by (iii),
f has a finite support J. If f were one–one, then there would be n /∈J such that
un ∈ran(f). Choose n′ /∈{n} ∪J and let g ∈G be the permutation of ω, which
interchanges n and n′ but leaves everything else undisturbed. If un = f( ˆm), then
un′ = ugn = gun = g(f( ˆm)) = (gf)(g ˆm) = f( ˆm) = un, contradicting un ̸= un′.
Thus there is no one–one map of ˆω into s, so that s is not Dedekind infinite.
Condition (iii) implies that the members of V (Γ) have the following property:
for x ∈V (B) let stab(x) = {g ∈G : gx = x}; then stab(x) ∈Γ for every
x ∈V (Γ), where Γ is the filter of subgroups generated by the Gn, that is,
Γ = {H : H a subgroup of G and for some finite J ⊆ω, [PDF-GLYPH-U+001C]
n∈J Gn ⊆H}. This
leads us to consider an (arbitrary) filter of subgroups of an (arbitrary) group G.

```

## PDF page 099 | printed page 79

```text
THE INDEPENDENCE OF THE AXIOM OF CHOICE
79
Finally, since we want G to act on V (Γ), we must have x ∈V (Γ) →gx ∈V (Γ) →
stab(gx) ∈Γ. But it is easy to verify that stab(gx) = gstab(x)g−1, so we shall
want Γ to satisfy H ∈Γ →gHg−1 ∈Γ for g ∈G. Under these conditions Γ is
said to be normal.
We now turn to the formal development. Let G be a group acting on the
complete Boolean algebra B, and let Γ be a filter of subgroups of G. That is, Γ
is a nonempty set of subgroups of G such that
H, K ∈Γ →H ∩K ∈Γ
and
H ∈Γ and H ⊆K, K a subgroup of G →K ∈Γ.
Γ is called a normal filter if
g ∈G and H ∈Γ →gHg−1 ∈Γ.
By Theorem 3.3, G acts on V (B); for each x ∈V (B) we define the stabilizer
of x by
stab(x) = {g ∈G : gx = x}.
It is easy to verify that stab(x) is subgroup of G. We define (by analogy with
(1.4)) the sets V (Γ)
α
recursively as follows:
V (Γ)
α
= {x : Fun(x) ∧ran(x) ⊆B ∧stab(x) ∈Γ ∧∃ξ < α[dom(x) ⊆V (Γ)
ξ
]}.
We put
V (Γ) = {x : ∃α(x ∈V (Γ)
α
)}.
It is now easy to verify that (cf. (1.6)):
x ∈V (Γ) ↔Fun(x) ∧ran(x) ⊆B ∧dom(x) ⊆V (Γ) ∧stab(x) ∈Γ,
and that
V (Γ) ⊆V (B).

```

## PDF page 100 | printed page 80

```text
80
GROUP ACTIONS AND INDEPENDENCE OF AC
For u, v ∈V (Γ) we define [[u ∈v]]Γ and [[u = v]]Γ recursively as we did
[[u ∈v]]B and [[u = v]]B, that is,
[[u ∈v]]Γ =
[PDF-GLYPH-U+0004]
x∈dom(v)
[v(x) ∧[[x = u]]Γ],
[[u = v]]Γ =
[PDF-GLYPH-U+0006]
x∈dom(u)
[u(x) ⇒[[x ∈v]]Γ] ∧
[PDF-GLYPH-U+0006]
y∈dom(v)
[v(y) ⇒[[x ∈u]]Γ].
It is then easily proved by induction that [[u ∈v]]Γ = [[u ∈v]]B, [[u = v]]Γ =
[[u = v]]B, and so [[· ∈·]]Γ, [[· = ·]]Γ turn V (Γ) into a B-valued structure. So if L(Γ)
is the language for V (Γ), that is, the result of expunging from L(B) all constant
symbols not denoting elements of V (Γ), the Boolean-value [[σ]]Γ in V (Γ) of any
L(Γ)-sentence σ is defined recursively by
[[σ ∧τ]]Γ = [[σ]]Γ ∧[[τ]]Γ
[[¬σ]]Γ = ([[σ]]Γ)∗
[[∃xφ(x)]]Γ =
[PDF-GLYPH-U+0004]
u∈V (Γ)
[[φ(u)]]Γ.
We shall need some technical facts about V (Γ).
Lemma 3.14 For every x ∈V ,
ˆx ∈V (Γ).
Proof By induction on ∈. Suppose ˆy ∈V (Γ) for every y ∈x. Then dom(ˆx) =
{ˆy : y ∈x} ⊆V (Γ) and by Theorem 3.3 we have gˆx = ˆx for very g ∈G, whence
stab(x) = G ∈Γ. Hence ˆx ∈V (Γ).
From now on we assume that Γ is a normal filter of subgroups of G.
Lemma 3.15 G acts on V (Γ).
Proof One first shows by induction on y ∈dom(x) that for any g ∈G, the
map x [PDF-GLYPH-U+0017]→gx carries V (Γ) into V (Γ). Suppose then that x ∈V (Γ) and gy ∈V (Γ)
for all y ∈dom(x). Then dom(gx) = {gy : y ∈dom(x)} ⊆V (Γ). Also, it is
readily verified that stab(gx) = gstab(x)g−1, and therefore stab(gx) ∈Γ by the
normality of Γ. Hence gx ∈V (Γ), completing the induction step.
Finally, since G acts on V (B), we have for any g ∈G, u, v ∈V (Γ),
g · [[u ∈v]]Γ = g · [[u ∈v]]B = [[gu ∈gv]]B = [[gu ∈gv]]Γ
and similarly for u = v. Therefore G acts on V (Γ) as claimed.

```

## PDF page 101 | printed page 81

```text
THE INDEPENDENCE OF THE AXIOM OF CHOICE
81
From
Lemma
3.15
and
(3.2)
it
follows
that,
for
every
formula
φ(v1, . . . , vn), all x1, . . . , xn ∈V (Γ) and all g ∈G,
g · [[φ(x1, . . . , xn)]]Γ = [[φ(gx1, . . . , gxn)]]Γ.
(3.16)
If P is a basis for B, we define, for any p ∈P and any L(Γ)-sentence σ,
p Γ-forces σ by
p ⊩Γ σ ↔p ≤[[σ]]Γ.
It follows immediately from (3.16) that for any formula φ(v1, . . . , vn), any
x1, . . . , xn ∈V (Γ) and any p ∈P, g ∈G for which gp ∈P,
p ⊩Γ φ(x1, . . . , xn) →gp ⊩Γ φ(gx1, . . . , gxn).
(3.17)
We define the notions of truth and validity in V (Γ) in the same way as we
defined those notions in V (B), for example, an L(Γ)-sentence σ is true in V (Γ)
(and we write V (Γ) |= σ) if [[σ]]Γ = 1.
The same argument as that used in the proof of Theorem 1.17 establishes
the following.
Theorem 3.18 Theorem 1.17 continues to hold when ‘B’ is replaced by ‘ Γ’.
We can now show that V (Γ) is a Boolean-valued model of ZF.
Theorem 3.19 All the axioms—and hence all the theorems—of ZF are true
in V (Γ).
Proof The axioms of extensionality and regularity go through as in Lemmas 1.34
and 1.42. As for the remaining axioms (with the exception of choice), the same
proofs as those given in Lemmas 1.35–1.38, Definition 1.39, Problem 1.40, and
Lemma 1.41 work, except that now one must verify that the object v required
to exist by the axiom in question has its stabilizer stab(v) in Γ. We do this in
detail for the axiom scheme of separation, confining ourselves to brief hints in
the case of other axioms.
Separation Let ψ(x, v1, . . . , vn) be a formula, and let u, a1, . . . , an ∈V (Γ) (thus
the a1, . . . , an are regarded as parameters). Define v ∈V (B) by dom(v) =
dom(u) and
v(x) = u(x) ∧[[ψ(x, a1, . . . , an)]]Γ
for x ∈dom(v). It now suffices to show that v ∈V (Γ), for then one readily
verifies as in Lemma 1.35 that
V (Γ) ⊨∀x[x ∈v ↔x ∈u ∧ψ(x, a1, . . . , an)].

```

## PDF page 102 | printed page 82

```text
82
GROUP ACTIONS AND INDEPENDENCE OF AC
Since dom(v) = dom(u) ⊆V (Γ), to show that v ∈V (Γ) it is enough to prove
that stab(v) ∈Γ. And since stab(u), stab(a1), . . . , stab(an) are all in Γ and Γ is
a filter, it will be enough to show that
A = stab(u) ∩stab(a1) ∩· · · ∩stab(an) ⊆stab(v).
(∗)
If g ∈A, then dom(gv) = {gx : x ∈dom(v)} = {gx : x ∈dom(u)} =
dom(gu) = dom(u) = dom(v). Also, if x ∈dom(v), then x = gy with y ∈dom(u)
so that
(gv)(x) = (gv)(gy)
= g · v(y)
= g · u(y) ∧[[ψ(gy, ga1, . . . , gan)]]Γ
(by (3.16))
= (gu)(gy) ∧[[ψ(x, a1, . . . , an)]]Γ
= u(x) ∧[[ψ(x, a1, . . . , an)]]Γ
= v(x).
Hence gv = v and g ∈stab(v). This proves (∗) and the result in question.
Replacement
In our original proof of the truth of this axiom in V (B)
(Lemma 1.36) we used a set of the form V (B)
α
× {1} to include the range of the
‘function’ defined by φ(x, y) on u. The same proof works here with V (B)
α
× {1}
replaced by V (Γ)
α
× {1}.
Union Given u ∈V (Γ), define v by dom(v) = [PDF-GLYPH-U+0015]{dom(y) : y ∈dom(u)} and
v(x) = [[∃y ∈u[x ∈y]]]Γ. One then verifies that stab(u) ⊆stab(v), so that v ∈
V (Γ). As in the original verification of the truth of the union axiom in V (B)
(Lemma 1.37) one shows that
V (Γ) |= ∀x[x ∈v ↔∃y ∈u[x ∈y]],
so that the axiom is true in V (Γ) as well.
Power Set. For u ∈V (Γ) define V by dom(v) = Bdom(u) ∩V (Γ) and v(x) =
[[x ⊆u]]Γ for x ∈dom(v). One can now show that stab(u) ⊆stab(v), so that
v ∈V (Γ). As in the original proof of the truth of the power set axiom in V (B)
(Lemma 1.38), one verifies that
V (Γ) |= ∀x[x ∈v ↔x ⊆u],
showing that the axiom is true in V (Γ) as well.
Infinity. We know that ˆω ∈V (Γ) (Lemma 3.14), so the argument here is the
same as in Lemma 1.41.

```

## PDF page 103 | printed page 83

```text
THE INDEPENDENCE OF THE AXIOM OF CHOICE
83
We now select specific B, G, and Γ in such a way that we have V (Γ) |= ¬AC.
It is clear that, if we can prove the existence of such B, G, and Γ in ZFC, then
in view of Theorems 3.18 and 3.19, the same argument as we used to prove
Theorem 1.19 implies that, if ZF is consistent, so is ZF + ¬AC.
Let X be the product space 2ω×ω and let B = RO(2ω×ω). Let G be the group
of all permutations of ω. G can be made to act on B in the following way. Each
g ∈G induces a homeomorphism g∗of X onto itself via
(g∗f)⟨m, n⟩= f⟨m, gn⟩
for f ∈X and m, n ∈ω. We define the action ⟨g, b⟩[PDF-GLYPH-U+0017]→gb of G on B by
gb = g∗−1[b]
= {f ∈X : g∗f ∈b}.
(It is readily checked that this does indeed define an action.)
For each n ∈ω let Gn = {g ∈G : gn = n}; clearly this is a subgroup of G.
Let Γ be the filter of subgroups generated by the Gn. That is, if for each finite
subset J ⊆ω we write
GJ =
[PDF-GLYPH-U+0007]
n∈J
Gn
then Γ is the set of all subgroups H of G such that GJ ⊆H for some finite
J ⊆ω. It is readily verified that Γ is normal.
Recalling that P = C(ω × ω, 2) is a basis for B, we now prove
Lemma 3.20 If p ∈P, J is a finite subset of ω and n /∈J, then there is g ∈GJ
such that p ∧gp ̸= 0 and gn ̸= n.
Proof Take n′ /∈J∪{n} so that ⟨m, n′⟩/∈dom(p) for any m (possible, since J and
dom(p) are finite) and let g ∈G be the permutation of ω, which interchanges
n and n′ but leaves everything else undisturbed. Then certainly g ∈GJ and
gn ̸= n. To see that p ∧gp ̸= 0, recall that p is identified with the element
N(p) = {f ∈2ω×ω : p ⊆f}
of B and observe that
g · N(p) = {f ∈2ω×ω : p ⊆g∗f}
= {f ∈2ω×ω : ⟨i, j⟩∈dom(p) →f⟨i, gj⟩= p⟨i, j⟩}.

```

## PDF page 104 | printed page 84

```text
84
GROUP ACTIONS AND INDEPENDENCE OF AC
Let i1, . . . , ik be a list of the i such that ⟨i, n⟩∈dom(p). Then
p ∧gp = N(p) ∩g · N(p)
= {f ∈2ω×ω : p ⊆f and f⟨ij, n′⟩= p⟨ij, n⟩for j = 1, . . . , k}
̸= ∅,
since ⟨ij, n′⟩/∈dom(p) for j = 1, . . . , k.
Now we can prove the following.
Theorem 3.21 With B, G, and Γ as above, we have V (Γ) |= ‘there is an infinite
Dedekind finite subset of P ˆω’ and so, a fortiori,
V (Γ) |= ¬AC.
Proof We write [[σ]] for [[σ]]Γ and ⊩for ⊩Γ throughout. For each n ∈ω define
un ∈Bdom(ˆω) by
un( ˆm) = {h ∈2ω×ω : h⟨m, n⟩= 1}.
The usual calculation shows that
V (B) |= un ⊆ˆω
for all n ∈ω. Moreover for all g ∈G and for all n ∈ω,
(1) gun = ugn.
For clearly we have dom(gun) = dom(ugn). Also, for m ∈ω,
(gun) ˆm = (gun)(g ˆm)
= g · un( ˆm)
= g∗−1[{h ∈2ω×ω : h⟨m, n⟩= 1}]
= {h ∈2ω×ω : g∗h⟨m, n⟩= 1}
= {h ∈2ω×ω : h⟨m, gn⟩= 1}
= ugn( ˆm),
and (1) follows.
(1) immediately gives Gn ⊆stab(un), so stab(un) ∈Γ and therefore un ∈
V (Γ). The argument in the proof of Theorem 2.12 gives:
(2) V (Γ) |= un ̸= un′,
for n ̸= n′.
Now put
s = {un : n ∈w} × {1};

```

## PDF page 105 | printed page 85

```text
THE INDEPENDENCE OF THE AXIOM OF CHOICE
85
it is then easy to see that gs = s for any g ∈G, so s ∈V (Γ). Moreover, it is not
hard to verify that V (Γ) |= s ⊆P ˆω. It now follows from (2) that
V (Γ) |= s is infinite.
We claim that
V (Γ) |= s is not Dedekind infinite,
which will prove the theorem. To establish the claim, it suffices to show that, for
each f ∈V (Γ),
[[Fun(f) ∧f is one–one ∧dom(f) = ˆω ∧ran(f) ⊆s]] = 0.
Suppose not; then there is p0 ∈P = C(ω × ω, 2) (the basis for B) such that
p0 || Fun(f) ∧f is one–one ∧dom(f) = ˆω ∧ran(f) ⊆s.
We shall find q ≤p0 such that
q ⊩¬Fun(f),
which will yield the desired contradiction.
We first observe that,
(3) p || x ∈s ↔∀q ≤p∃r ≤q∃n ∈ω[r ⊩x = un].
For we have
p || x ∈s ↔p ≤
[PDF-GLYPH-U+0004]
n∈ω
[[x = un]]
↔p ∧
[PDF-GLYPH-U+0006]
n∈ω
[[x ̸= un]] = 0
↔∀q ≤p
[PDF-GLYPH-U+001D]
q ≰
[PDF-GLYPH-U+0006]
n∈ω
[[x ̸= un]]
[PDF-GLYPH-U+001E]
↔∀q ≤p∃n ∈ω[q ≰[[x ̸= un]]]
↔∀q ≤p∃n ∈ω¬[q ⊩x ̸= un]
↔∀q ≤p∃n ∈ω∃r ≤q[r || x = un].
Now since f ∈V (Γ) it has a finite support J, that is, there is a finite subset
J ⊆ω such that GJ ⊆stab(f). Let
J = {n1, . . . , nj}.

```

## PDF page 106 | printed page 86

```text
86
GROUP ACTIONS AND INDEPENDENCE OF AC
Since p0 || f is one–one ∧Fun(f), it follows that
p0 || ∃x ∈ˆω[f(x) ̸= un1 ∧· · · ∧f(x) ̸= unj]
so that there is p ≤p0 and m ∈w such that,
(4) p || f( ˆm) ̸= un1 ∧· · · ∧f( ˆm) ̸= unj.
Since p0 || f( ˆm) ∈s, so that p || f( ˆm) ∈s, by (3) there is r ≤p and n ∈ω
such that,
(5) r || f( ˆm) = un.
But (4) implies
r || f( ˆm) ̸= un1 ∧· · · ∧f( ˆm) ̸= unj
and this, together with (5), implies n ̸= n1 ∧· · · ∧n ̸= nj, that is, n /∈J. By
Lemma 3.20 there is g ∈GJ such that p∧gp = 0 and gn ̸= n. It follows from (5)
and (3.17) that
gr || (gf)g ˆm = gun.
But this, together with (1) and the fact that g ∈GJ ⊆stab(f) gives
gr || f( ˆm) = ugn.
Since r ∧gr ̸= 0, there is q ∈P such that q ≤r and q ≤gr. Then q ≤p0 and
q || f( ˆm) = un ∧f( ˆm) = ugn.
But since gn ̸= n, we have, using (2), [[ugn ̸= un]] = 1, so that q || ugn ̸= un.
Therefore
q || ¬Fun(f),
and the proof is complete.
Corollary 3.22 If ZF is consistent, so is ZF + ¬AC.
We concluded this chapter with some remarks on the origins of the proof
of Theorem 3.21. The construction of V (Γ) is in fact derived from an earlier
construction, due to Fraenkel and Mostowski, which was used to show that AC
is independent of a certain modified form of ZF, namely, the theory ZFA of
set theory with atoms. (This is actually a weaker result because the axiom of
foundation does not hold in ZFA.) To obtain ZFA from ZF, one drops the axiom
of foundation, and adds an axiom asserting the existence of a nonempty set A

```

## PDF page 107 | printed page 87

```text
THE INDEPENDENCE OF THE AXIOM OF CHOICE
87
of atoms, that is, objects lacking members, yet not identical with the empty
set. The axiom of extensionality must also be suitably modified. The method
of Fraenkel–Mostowski now runs roughly as follows. One first shows that the
permutation group G of A acts on the universe V by ∈-automorphisms. Then,
letting Γ be a normal filter in G, one constructs V (Γ) essentially as before and
shows that it is a model of ZFA. By choosing A and Γ properly, one can arrange
things so that in V (Γ) the set A is not well-orderable. This will be so essentially
because the presence in V (Γ) of so many automorphisms permuting the elements
of A will make these elements effectively indiscernible in V (Γ) and thereby render
it impossible to chooe a ‘first element’ of A. (For more on Fraenkel–Mostowski
models, see Felgner (1971) or Jech (1973).)
The method we have presented for proving the independence of AC from ZF
combines the Fraenkel–Mostowski technique with that of Boolean-valued models.
In a nutshell, a set of ‘reals’ in V (Γ) (the set {un : n ∈ω}) is found, which behaves
very much like a set of atoms; then one argues `a la Fraenkel–Mostowski. It turns
out that many Fraenkel–Mostowski proofs of independence from ZFA can be
converted in this way into proofs of independence from ZF, for example, those
of ‘every set can be linearly ordered’, ‘every countable set of pairs has a choice
function’, ‘every vector space has a basis’. See Jech (1973).

```

## PDF page 108 | printed page 88

```text
4
GENERIC ULTRAFILTERS AND TRANSITIVE
MODELS OF ZFC
In this chapter we replace V by a (transitive) model M of ZFC such that M ∈V ,
and perform the construction of V (B) and [PDF-GLYPH-U+0001]·[PDF-GLYPH-U+0002]B inside M. We shall see that this
construction gives rise to models of ZFC in which one can falsify the various
set-theoretic assertions whose formal independence of ZFC was establised in
earlier chapters. In this way Boolean-valued set theory can be transformed into
a valuable model-theoretic tool.
Now let M be a transitive ∈-model of ZFC and let B ∈M be a complete
Boolean algebra in the sense of M. That is,
M |= B is a complete Boolean algebra.
In particular, if X ∈PB ∩M, then [PDF-GLYPH-U+0003] X and [PDF-GLYPH-U+0002] X exist and are in M. (Notice
that PB ∩M is the power set of B formed in M, P (M)(B).) Moreover, since the
predicate ‘B is a Boolean algebra’ is a restricted formula, it follows that B is a
Boolean algebra (but not necessarily complete) ‘from the outside’ as well.
Under these conditions we can relativize all the notions and constructions of
Chapter 1 to M. We write M (B) for (V (B))(M) and L(B)
M
for (L(B))(M) . M (B) is
called the B-extension of M: all the results proved in Chapter 1 for V (B) hold,
mutatis mutandis, for M (B). We also obtain a Boolean truth value ([PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B)(M) ∈B
for each L(B)
M -sentence σ: to simplify the notation we agree to write [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002] for
([PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B)(M). Writing M (B) |= σ for [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002] = 1, we see from Theorem 1.33 that
M (B) |= σ whenever σ is an axiom of ZFC, so that M (B) may be thought of
as a Boolean-valued model of ZFC. Finally, by analogy with Definition 1.22, we
obtain a mapˆ: M →M B such that, for each x ∈M,
ˆx = {⟨ˆy, 1⟩: y ∈x}.
Now suppose that U is an arbitrary but fixed ultrafilter in B. In general, U is
not a member of M. Define the relation ∼U on M (B) by putting, for x, y ∈M (B),
x ∼U y ↔[PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002] ∈U.

```

## PDF page 109 | printed page 89

```text
GENERIC ULTRAFILTERS AND MODELS OF ZFC
89
It is easy to verify that ∼U is an equivalence relation on M (B). For x ∈M (B),
write xU for the ∼U-class of x, that is,
xU = {y ∈M (B) : x ∼U y},
and define the relation ∈U on the set of all ∼U-classes by
xU ∈U yU ↔[PDF-GLYPH-U+0001]x ∈y[PDF-GLYPH-U+0002] ∈U.
Now define the quotient of M (B) by U to be the structure
M (B)/U = ⟨{xU : x ∈M (B)}, ∈U⟩.
Theorem 4.1 For any formula φ(v1, . . . , vn) and any x1, . . . , xn ∈M (B),
M (B)/U |= φ[xU
1 , . . . , xU
n ] ↔[PDF-GLYPH-U+0001]φ(x1, . . . , xn)[PDF-GLYPH-U+0002] ∈U.
Proof Induction on the complexity of φ, using the Maximum Principle to handle
the existential case. We omit the straightforward details.
Corollary 4.2 M (B)/U is a model of ZFC. More generally, for any sentence
σ, if M (B) |= σ, then M (B)/U |= σ.
Let S ⊆P (M)(B) = PB ∩M. Recall (Chapter 0) that U is said to be
S-complete if, for all X ∈S,
[PDF-GLYPH-U+0004]
X ∈U →X ∩U ̸= ∅
(the reverse implication holding trivially). A P (M)(B)-complete ultrafilter is
called M-generic.
A partition of unity {ai : i ∈I} in B is called an M-partition of unity in B if
⟨ai : i ∈I⟩∈M. We have the following simple characterization of M-genericity
in terms of this notion:
Lemma 4.3 The following conditions are equivalent:
(i) U is M-generic;
(ii) for any M-partition of unity {ai : i ∈I} in B, there is i ∈I such that
ai ∈U.
Proof (i) →(ii) is clear. Conversely, assume (ii) and let A ∈P (M)(B). Since the
axiom of choice holds in M, there is an ordinal α ∈M such that A∪{([PDF-GLYPH-U+0003] A)∗} =
{aξ : ξ < α}. Now put bξ = aξ −[PDF-GLYPH-U+0003]
η<ξ aη for ξ < α. Then {bξ : ξ < α} is an
M-partition of unity in B and so by (ii) there is ξ < α such that bξ ∈U. It is
now easy to see that [PDF-GLYPH-U+0003] A ∈U →U ∩A ̸= ∅. Hence U is a M-generic.

```

## PDF page 110 | printed page 90

```text
90
GENERIC ULTRAFILTERS AND MODELS OF ZFC
An element α ∈M (B)/U is called an ordinal in M (B)/U if M (B)/U |= Ord[α].
It follows immediately from Theorem 4.1 that if α is an ordinal in M then ˆαU is
an ordinal in M (B)/U; elements of the latter form are called standard ordinals
in M (B)/U.
Let ORD(M) be the set of all ordinals in M (thus ORD(M) = ORD ∩M).
Then for x ∈M (B) the set
{[PDF-GLYPH-U+0001]x = ˆα[PDF-GLYPH-U+0002] : α ∈ORD(M)}
(4.4)
is a subset of B which is definable in M (from the parameter x) and is therefore
a member of M. Let S1 be the subfamily of P (M)(B) consisting of all sets of the
form (4.4) for x ∈M (B). By Theorem 1.44 we have, for x ∈M (B),
[PDF-GLYPH-U+0001]Ord(x)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
α∈ORD(M)
[PDF-GLYPH-U+0001]x = ˆα[PDF-GLYPH-U+0002].
(4.5)
We use this in the proof of
Theorem 4.6 The following conditions are equivalent:
(i) U is S1-complete;
(ii) all ordinals in M (B)/U are standard;
(iii) U is M-generic.
Proof (i) →(iii) Assume (i) and let {aξ : ξ < α} be an M-partition of unity in
B, where α ∈ORD(M). (Since the axiom of choice holds in M there is no loss of
generality in assuming the partition of unity to be indexed by an ordinal α.) By
Problem 1.26(i), there is x ∈M (B) such that aξ = [PDF-GLYPH-U+0001]x = ˆξ[PDF-GLYPH-U+0002] for ξ < α. We have
[PDF-GLYPH-U+0004]
ξ∈ORD(M)
[PDF-GLYPH-U+0001]x = ˆξ[PDF-GLYPH-U+0002] ≥
[PDF-GLYPH-U+0004]
ξ<α
[PDF-GLYPH-U+0001]x = ˆξ[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
ξ<α
aξ = 1 ∈U,
so that, by (i), there is η ∈ORD(M) such that [PDF-GLYPH-U+0001]x = ˆη[PDF-GLYPH-U+0002] ∈U. If η ≥α, then
[PDF-GLYPH-U+0001]x = ˆη[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]x = ˆη[PDF-GLYPH-U+0002] ∧1 = [PDF-GLYPH-U+0001]x = ˆη[PDF-GLYPH-U+0002] ∧
[PDF-GLYPH-U+0004]
ξ<α
[PDF-GLYPH-U+0001]x = ˆξ[PDF-GLYPH-U+0002] = 0 /∈U,
so that we must have η < α. Hence aη = [PDF-GLYPH-U+0001]x = ˆη[PDF-GLYPH-U+0002] ∈U and (iii) follows by
Lemma 4.3.

```

## PDF page 111 | printed page 91

```text
GENERIC ULTRAFILTERS AND MODELS OF ZFC
91
(iii) →(ii) Assume (iii); then, using (4.5) and Theorem 4.1,
M (B)/U |= Ord[xU] ↔[PDF-GLYPH-U+0001]Ord(x)[PDF-GLYPH-U+0002] ∈U
↔
[PDF-GLYPH-U+0004]
α∈ORD(M)
[PDF-GLYPH-U+0001]x = ˆα[PDF-GLYPH-U+0002] ∈U
↔[PDF-GLYPH-U+0001]x = ˆα[PDF-GLYPH-U+0002] ∈U for some α ∈ORD(M)
↔xU = ˆαUfor some α ∈ORD(M).
(ii) →(i) Assume (ii); then if [PDF-GLYPH-U+0003]
α∈ORD(M)[PDF-GLYPH-U+0001]x = ˆα[PDF-GLYPH-U+0002] ∈U, we have [PDF-GLYPH-U+0001]Ord(x)[PDF-GLYPH-U+0002] ∈U
by (4.5), so M (B)/U |= Ord[xU] by Theorem 4.1. Hence (ii) gives xU = ˆαU for
some α ∈ORD(M), whence [PDF-GLYPH-U+0001]x = ˆα[PDF-GLYPH-U+0002] ∈U.
Corollary 4.71 If U is M-generic, then ∈U is a well-founded relation.
Proof If U is M-generic, then Theorem 4.6 implies that the map α [PDF-GLYPH-U+0017]→ˆαU sends
the well-ordered set ORD(M) onto the set of ordinals in M (B)/U. This map is
easily seen to be order-preserving (with respect to ∈U) and it follows that the
ordinals of M (B)/U are well-ordered by ∈U. The usual rank argument now shows
that ∈U is well-founded on M (B)/U: if not, then there would be an infinite des-
cending ∈U-sequence . . . x2 ∈U x1 ∈U x0; if ρ is the rank function in M (B)/U,
then . . ., ρ(x2), ρ(x1), ρ(x0) would be an infinite descending sequence of ordinals
in M (B)/U, contradicting the fact that these are well-ordered.
Suppose now that ∈U is a well-founded relation. Then, by Mostowski’s col-
lapsing lemma, M (B)/U can be collapsed to a unique transitive ∈-structure M[U]
via the map h defined recursively on ∈U by
h(xU) = {h(yU) : yU ∈U xU} = {h(yU) : [PDF-GLYPH-U+0001]y ∈x[PDF-GLYPH-U+0002] ∈U}.
(4.8)
Thus h : M (B)/U →M[U] is a bijection satisfying
xU ∈U yU ↔h(xU) ∈h(yU).
We can now define a map i of M (B) onto M[U] by putting
i(x) = h(xU)
(4.9)
for x ∈M (B). By (4.8) we have, for x ∈M (B),
i(x) = {i(y) : [PDF-GLYPH-U+0001]y ∈x[PDF-GLYPH-U+0002] ∈U}.
(4.10)
1The converse of Corollary 4.7 fails: see Problem 4.32.

```

## PDF page 112 | printed page 92

```text
92
GENERIC ULTRAFILTERS AND MODELS OF ZFC
The map i—which we sometimes write as iU—is called the canonical map of
M (B) onto M[U].
Lemma 4.11 For any formula φ(v1, . . . , vn) and any x1, . . . , xn ∈M (B),
M[U] |= φ[i(x1), . . . , i(xn)] ↔[PDF-GLYPH-U+0001]φ(x1, . . . , xn)[PDF-GLYPH-U+0002] ∈U.
Proof Immediate from Theorem 4.1 and the fact that h is an isomorphism of
M (B)/U onto M[U].
Now define j : M →M[U] by
j(x) = i(ˆx)
(4.12)
for x ∈M. We see immediately from Theorem 1.23 that j is a one–one map
satisfying x ∈y ↔j(x) ∈j(y); that is, j is an ∈-monomorphism of M into
M[U]. The situation can be depicted by the commutative diagram:
M
·^
·U
M(B)
M[U]
j
h
i
M(B)/U
If x ∈M (B), y ∈M, the set
{[PDF-GLYPH-U+0001]x = ˆz[PDF-GLYPH-U+0002] : z ∈y}
(4.13)
is a subset of B which is definable in M (from the parameters x, y) and is
accordingly a member of M. Let S2 be the subfamily of P (M)(B) consisting of
all sets of the form (4.13) for x ∈M (B), y ∈M. We recall from Theorem 1.23(i)
that, for x ∈M (B), y ∈M,
[PDF-GLYPH-U+0001]x ∈ˆy[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
z∈y
[PDF-GLYPH-U+0001]x = ˆz[PDF-GLYPH-U+0002].
(4.14)
We use this in the proof of the following.
Theorem 4.15 The following conditions are equivalent:
(i) U is S2-complete;
(ii) ∈U is well-founded and j is the identity on M;
(iii) ∈U is well-founded and j[M] is transitive;
(iv) U is M-generic.

```

## PDF page 113 | printed page 93

```text
GENERIC ULTRAFILTERS AND MODELS OF ZFC
93
Proof The equivalence of (ii) and (iii) follows easily from the transitivity of M
and the fact that, by construction, j is an ∈-isomorphism of M onto j[M].
(i) →(iv). Assume (i), and let {ai : i ∈I} be an M-partition of unity in B.
By Problem 1.26(i) there is x ∈M (B) such that ai = [PDF-GLYPH-U+0001]x = ˆai[PDF-GLYPH-U+0002] for i ∈I. Putting
{ai : i ∈I} = y ∈M, we have
[PDF-GLYPH-U+0004]
z∈y
[PDF-GLYPH-U+0001]x = ˆz[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
i∈I
[PDF-GLYPH-U+0001]x = ˆai[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
i∈I
ai = 1 ∈U.
Therefore, by (i), there is z ∈y such that [PDF-GLYPH-U+0001]x = ˆz[PDF-GLYPH-U+0002] ∈U. But z = ai for some
i ∈I, whence ai = [PDF-GLYPH-U+0001]x = ˆai[PDF-GLYPH-U+0002] ∈U. (iv) now follows from Lemma 4.3.
(iv) →(iii). Assume (iv). Then ∈U is well-founded by Corollary 4.7. Also,
if y ∈M and x ∈j(y), then, since M[U] is transitive, there is x′ ∈M (B) such
that x = i(x′). Thus i(x′) ∈j(y) = i(ˆy), so that, by (4.10), [PDF-GLYPH-U+0001]x′ ∈ˆy[PDF-GLYPH-U+0002] ∈U.
It follows now from (iv) and (4.14) that there is z ∈y, hence z ∈M, such that
[PDF-GLYPH-U+0001]x′ = ˆz[PDF-GLYPH-U+0002] ∈U, whence x = j(z) ∈j[M], and (iii) follows.
(iii) →(i). Assume (iii). If x ∈M (B), y ∈M, then
[PDF-GLYPH-U+0004]
z∈y
[PDF-GLYPH-U+0001]x = ˆz[PDF-GLYPH-U+0002] ∈U →[PDF-GLYPH-U+0001]x ∈ˆy[PDF-GLYPH-U+0002] ∈U
(by (4.14))
→xU ∈U ˆyU
→h(xU) ∈h(ˆyU)
→i(x) ∈i(ˆy) = j(y)
→i(x) = j(z) for some z ∈M
(by (iii))
→j(z) ∈j(y)
→z ∈y.
Hence i(x) = j(z) = i(ˆz), so by definition of i (4.9), [PDF-GLYPH-U+0001]x = ˆz[PDF-GLYPH-U+0002] ∈U. (i) follows.
Corollary 4.16 If U is M-generic, then M ⊆M[U].
Next, we define U∗∈M (B) by dom(U∗) = {ˆx : x ∈B} = dom( ˆB) and
U∗(ˆx) = x for x ∈B. Notice that U∗does not depend on U. We have for
x ∈M (B),
[PDF-GLYPH-U+0001]x ∈U∗[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
y∈B
[y ∧[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002]],
(4.17)
and, for x ∈B,
[PDF-GLYPH-U+0001]ˆx ∈U∗[PDF-GLYPH-U+0002] = x.
(4.18)

```

## PDF page 114 | printed page 94

```text
94
GENERIC ULTRAFILTERS AND MODELS OF ZFC
In particular, if σ is any B-sentence, we have [PDF-GLYPH-U+0001][PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]ˆ ∈U∗[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002], that is,
M (B) |= [[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]ˆ ∈U∗↔σ].
In other words, U∗represents the truth values of ‘true’ sentences in M (B).
Let S3 be the subfamily of P (M)(B) consisting of all subsets of B of the form
{y ∧[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] : y ∈B} for x ∈M (B). Then we have
Theorem 4.19 The following conditions are equivalent:
(i) U is S3-complete;
(ii) ∈U is well-founded, j is the identity on U, and i(U∗) = U;
(iii) U is M-generic.
Proof (i) →(iii). Assume (i). Let {ai : i ∈I} be an M-partition of unity in B.
By Problem 1.26(i) there is x ∈M (B) such that ai = [PDF-GLYPH-U+0001]x = ˆai[PDF-GLYPH-U+0002] for i ∈I. Hence
[PDF-GLYPH-U+0004]
y∈B
[y ∧[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002]] ≥
[PDF-GLYPH-U+0004]
i∈I
[ai ∧[PDF-GLYPH-U+0001]x = ˆai[PDF-GLYPH-U+0002]] =
[PDF-GLYPH-U+0004]
i∈I
ai = 1 ∈U,
and so by (i) there is y ∈B such that y ∧[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] ∈U. If y /∈{ai : i ∈I} then
[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] ∧1 = [PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] ∧
[PDF-GLYPH-U+0004]
i∈I
[PDF-GLYPH-U+0001]x = ˆai[PDF-GLYPH-U+0002] = 0 /∈U,
so that there must be i ∈I such that y = ai. But then ai = ai ∧[PDF-GLYPH-U+0001]x = ˆai[PDF-GLYPH-U+0002] ∈U
and so (iii) follows by Lemma 4.3.
(iii) →(ii). Assume (iii). Then by Theorem 4.15 ∈U is well-founded and j is
the identity on M, hence on U. We claim that, for x ∈M (B),
{i(x) : [PDF-GLYPH-U+0001]x ∈U∗[PDF-GLYPH-U+0002] ∈U} = {i(ˆy) : y ∈U}.
(1)
This follows from the chain of equivalences
[PDF-GLYPH-U+0001]x ∈U∗[PDF-GLYPH-U+0002] ∈U ↔
[PDF-GLYPH-U+0004]
y∈B
[y ∧[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002]] ∈U
(by (4.17))
↔∃y ∈B[y ∧[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] ∈U]
(by (iii))
↔∃y ∈U[[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] ∈U]
↔∃y ∈U[i(x) = i(ˆy)].

```

## PDF page 115 | printed page 95

```text
GENERIC ULTRAFILTERS AND MODELS OF ZFC
95
Now we have
i(U∗) = {i(x) : [PDF-GLYPH-U+0001]x ∈U∗[PDF-GLYPH-U+0002] ∈U}
(by (4.10))
= {i(ˆy) : y ∈U}
(by (1))
= {j(y) : y ∈U}
= {y : y ∈U} = U,
and this gives (ii).
(ii) →(i). Assuming (ii) we have, using (4.10)
U = i(U∗) = {i(x) : [PDF-GLYPH-U+0001]x ∈U∗[PDF-GLYPH-U+0002] ∈U}.
(2)
Hence
[PDF-GLYPH-U+0004]
y∈B
[y ∧[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002]] ∈U →[PDF-GLYPH-U+0001]x ∈U∗[PDF-GLYPH-U+0002] ∈U
(by (4.17))
→i(x) ∈U
(by (2))
→i(x) = y = j(y) for some y ∈U
(by (ii))
→i(x) = i(ˆy)
→[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] ∈U
→y ∧[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] ∈U
and (i) follows.
Theorem 4.19 immediately gives the following.
Corollary 4.20 If U is M-generic, then U ∈M[U].
We now show that U∗is an ‘M-generic ultrafilter’ in the sense of M (B).
Given a Boolean algebra A and a subset F ⊆PA, we say that A is F-complete
if for all X ∈F, [PDF-GLYPH-U+0003] X and [PDF-GLYPH-U+0002] X exist in A. Thus our given Boolean algebra B is
P (M)(B)-complete. Since the predicate ‘A is an F-complete Boolean algebra’ is
clearly a restricted formula (with parameters A and F), it follows that, using
Theorem 1.23,
M (B) |= ˆB is a (P (M)(B))ˆ-complete Boolean algebra,
and furthermore we have the following.

```

## PDF page 116 | printed page 96

```text
96
GENERIC ULTRAFILTERS AND MODELS OF ZFC
Theorem 4.21 M (B) |= U∗is a (P (M)(B))[PDF-GLYPH-U+0001]-complete ultrafilter in ˆB.
Proof Let us put C = ˆB. Then we know that
M (B) |= C is a (P (M)(B))[PDF-GLYPH-U+0001]-complete Boolean algebra.
Let us denote the Boolean operations in C by ∧C, ∗c, [PDF-GLYPH-U+0003]
C, etc. and the natural
partial ordering in C by ≤C. It is then easy to see that, for any a, b ∈B, A ⊆B,
we have
[PDF-GLYPH-U+0001]ˆa ∧C ˆb = (a ∧b)[PDF-GLYPH-U+0001][PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]ˆa
∗C = (a∗)[PDF-GLYPH-U+0001][PDF-GLYPH-U+0002] = 1
[PDF-GLYPH-U+0003] [PDF-GLYPH-U+0004]
C
ˆA =
[PDF-GLYPH-U+001F][PDF-GLYPH-U+0004]
A
 [PDF-GLYPH-U+0001] [PDF-GLYPH-U+0004]
= 1.
We turn now to the properties of U∗. To prove the theorem it will be enough to
verify the assertions (a)–(e) below.
(a) [PDF-GLYPH-U+0001]U∗⊆C ∧ˆ0 /∈U∗[PDF-GLYPH-U+0002] = 1. This follows in a straightforward way from (4.17)
and (4.18).
(b) [PDF-GLYPH-U+0001]∀xy ∈C[x, y ∈U∗→x ∧C y ∈U∗][PDF-GLYPH-U+0002] = 1. To verify this, notice that the
l.h.s. is
[PDF-GLYPH-U+0006]
a,b∈B
[[PDF-GLYPH-U+0001]ˆa ∈U∗∧ˆb ∈U∗[PDF-GLYPH-U+0002] ⇒[PDF-GLYPH-U+0001]ˆa ∧C ˆb ∈U∗[PDF-GLYPH-U+0002]]
=
[PDF-GLYPH-U+0006]
a,b∈B
[[PDF-GLYPH-U+0001]ˆa ∈U∗∧ˆb ∈U∗[PDF-GLYPH-U+0002] ⇒(a ∧b)[PDF-GLYPH-U+0001]∈U∗[PDF-GLYPH-U+0002]]
=
[PDF-GLYPH-U+0006]
a,b∈B
[a ∧b ⇒a ∧b] = 1.
(c) [PDF-GLYPH-U+0001]∀xy ∈C[y ∈U∗∧y ≤C x →x ∈U∗][PDF-GLYPH-U+0002] = 1. The proof of this is similar to
(b), and is left to the reader.
(d) [PDF-GLYPH-U+0001]∀x ∈C[x ∈U∗∨x
∗C ∈U∗][PDF-GLYPH-U+0002]. The proof of this is also similar to (b).
(e) [PDF-GLYPH-U+0001]U∗is (P (M)(B))[PDF-GLYPH-U+0001] -complete[PDF-GLYPH-U+0002] = 1. Now the l.h.s. here is
[PDF-GLYPH-U+0003]
∀X ∈(P (M)(B))[PDF-GLYPH-U+0001] ![PDF-GLYPH-U+0004]
X ∈U∗→U∗∩X ̸= ∅
"[PDF-GLYPH-U+0004]
=
[PDF-GLYPH-U+0006]
A∈P (M)(B)
[PDF-GLYPH-U+0003] [PDF-GLYPH-U+0004]
C
ˆA ∈U∗→U∗∩ˆA ̸= ∅
[PDF-GLYPH-U+0004]

```

## PDF page 117 | printed page 97

```text
GENERIC ULTRAFILTERS AND MODELS OF ZFC
97
and this last expression = 1, in view of the fact that, for any A ∈P (M)(B),
[PDF-GLYPH-U+0003] [PDF-GLYPH-U+0004]
C
ˆA ∈U∗
[PDF-GLYPH-U+0004]
=
[PDF-GLYPH-U+0003] [PDF-GLYPH-U+001F][PDF-GLYPH-U+0004]
A
 [PDF-GLYPH-U+0001]
∈U∗
[PDF-GLYPH-U+0004]
=
[PDF-GLYPH-U+0004]
A
=
[PDF-GLYPH-U+0004]
a∈A
[PDF-GLYPH-U+0001]ˆa ∈U∗[PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]∃x ∈ˆA(x ∈U∗)[PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]U∗∩ˆA ̸= ∅[PDF-GLYPH-U+0002].
In view of Theorem 4.21, U∗is called the canonical generic ultrafilter in M (B)
(or in ˆB): if U is a generic ultrafilter in B, we see from Theorem 4.19 that U∗is
the natural preimage of U under the map iU : M (B) →M[U].
If U is an M-generic ultrafilter in B, M[U] is called a generic extension
of
M.
We
can
now
give
an
invariant
characterization
of
M[U]
for
generic U.
Theorem 4.22 Let U be an M-generic ultrafilter in B. Then:
(i) M[U] is a transitive ∈-model of ZFC;
(ii) M[U] is the least transitive ∈-model of ZF which includes M and
contains U;
(iii) M and M[U] have the same ordinals and constructible sets.
Proof (i) Since M[U] is, by construction, isomorphic to M(B)/U, (i) is an
immediate consequence of Corollary 4.2.
(ii) Let N be a transitive ∈-model of ZF such that M ⊆N and U ∈N.
For each α ∈ORD(M), put M (B)
α
= (V (B)
α
)(M); then clearly M (B)
α
∈M ⊆N
and M (B) = [PDF-GLYPH-U+0015]{M (B)
α
: α ∈ORD(M)}. Inspection of the definition of the col-
lapsing map i reveals that i|M (B)
α
, the restriction of i to M (B)
α
, can be defined
in N from U; it follows that ran(i|M (B)
α
) ∈N, and, since N is transitive, that
ran(i|M (B)
α
) ⊆N. Hence
M[U] =
[PDF-GLYPH-U+0005]
{ran(i|M (B)
α
: α ∈ORD(M)} ⊆N.
This proves (ii).

```

## PDF page 118 | printed page 98

```text
98
GENERIC ULTRAFILTERS AND MODELS OF ZFC
(iii) Let y ∈M[U]; then y = i(x) for some x ∈M (B) and we have
M[U] |= Ord[y]
↔M[U] |= Ord[i(x)]
↔[PDF-GLYPH-U+0001]Ord(x)[PDF-GLYPH-U+0002] ∈U
(by Lemma 4.11)
↔
[PDF-GLYPH-U+0004]
α∈ORD(M)
[PDF-GLYPH-U+0001]x = ˆα[PDF-GLYPH-U+0002] ∈U
(by (4.5))
↔∃α ∈ORD(M)[[PDF-GLYPH-U+0001]x = ˆα[PDF-GLYPH-U+0002] ∈U]
(since U is generic)
↔∃α ∈ORD(M)[y = i(x) = i(ˆα) = α]
(by Theorem 4.15)
↔y ∈ORD(M).
Thus M and M[U] have the same ordinals. That M and M[U] have the same
constructible sets is proved similarly, now using Theorem 1.46 (in M).
In view of (ii) of this theorem, M[U] may be termed the model of ZFC
obtained by adjoining U to M, or generated by U and M.
Under what conditions do M-generic ultrafilters exist? The following simple
example shows that if M is uncountable one cannot in general establish the
existence of generic ultrafilters. Let M be an uncountable transitive ∈-model of
ZFC such that ω1 ∈M, and put B = RO(ωω
1 )(M). By Corollary 5.2 to be proved
in Chapter 5, M (B) |= ˆω1 is countable. So if U were an M-generic ultrafilter in
B, we would have M[U] |= ω1 is countable and hence, since ω1 ∈M ⊆M[U], ω1
would also be countable in the real world. This contradiction shows that there
are no M-generic ultrafilters in B.
The situation is quite different, however, when M is countable.
Theorem 4.23 If M is countable, (or, more generally, if P (M)(B) is countable)
then for each b ̸= 0 in B there is an M-generic ultrafilter in B containing b.
Proof If M is countable, then so is P (M)(B), and the Rasiowa–Sikorski theorem
(Theorem 0.6) applies.
Corollary 4.24 Let σ be any sentence and suppose that in L we can define a
constant term t such that
ZF + V = L ⊢[t is a complete Boolean algebra and V (t) |= σ].
Then, given any countable transitive ∈-model of ZF, we can construct a countable
transitive ∈-model of ZFC + σ.
Proof Let N be a countable transitive model of ZF, and let M be the submodel
of N consisting of all members of N which are constructible in N, that is,

```

## PDF page 119 | printed page 99

```text
GENERIC ULTRAFILTERS AND MODELS OF ZFC
99
M = {x ∈N : N |= L[x]}. It is well-known that M is then a transitive model of
ZF + V = L. Let B = t(M); then B is a complete Boolean algebra in the sense
of M and M (B) |= σ. Let U be an M-generic ultrafilter in B, which exists by
Theorem 4.23. Then [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B = 1 ∈U, so that M[U] |= σ, and M[U] is the required
model.
It follows immediately from this corollary and the results of Chapter 2 that,
given a countable transitive ∈-model M of ZF, we can construct countable
transitive ∈-models of, for example,
ZFC + GCH + Pω ⊈L
(Theorem 2.8, 2.6),
ZFC + 2ℵ0 = ℵ2 + ∀κ ≥ℵ1[2κ = κ+]
(Problem 2.19),
ZFC + 2ℵ0 = ℵ1 + 2ℵ1 = ℵω+1
(Problem 2.20),
ZFC + GCH + Pω ⊆L + Pω1 ⊈L
(Problem 2.21).
We conclude this chapter by showing how results about M (B) can be
‘transferred’ to V (B). The possibility of doing is based on the following.
Lemma 4.25 Let Trans(M) be the formula expressing ‘M is transitive’. Let φ(x)
be a formula with one free variable x and suppose that there is a finite conjunction
τ1∧· · · ∧τn = τ of axioms of ZFC such that
⊢[Trans(M) ∧|M| = ℵ0 ∧τ (M)]
→[∀B[B is a complete Boolean algebra →φ(B)]](M).
(1)
Then
ZFC ⊢∀B[B is a complete Boolean algebra →φ(B)].
Proof Let σ be the sentence
∀B[B is a complete Boolean algebra →φ(B)].
Then, by the reflection principle and the downward L¨owenheim–Skolem theorem,
we have
ZFC ⊢∃M[Trans(M) ∧|M| = ℵ0 ∧τ (M) ∧(σ(M) ↔σ)].
The result now follows immediately from (1).
This lemma enables us to ‘transfer’ to V results about V (B) derived in M (i.e.
results about M (B)) in the following way. Suppose that Φ(V (B)) is some first-
order statement about V (B), which is expressible as a formula φ(B). Then, if we

```

## PDF page 120 | printed page 100

```text
100
GENERIC ULTRAFILTERS AND MODELS OF ZFC
can show that Φ(V (B)) holds in each countable transitive model of some finite
conjunction of axioms of ZFC, it will follow from the lemma that Φ(V (B)) is a
theorem of ZFC, that is, Φ(V (B)) ‘holds in V ’.
This technique can be applied to elucidate the nature of the canonical generic
ultrafilter U∗. First, we note that the same definition of U∗with M replaced by
V makes U∗a member of V (B); so we may refer to U∗also as the canonical
generic ultrafilter in V (B).
Next, we introduce a new constant symbol ˆV into L(B), it being under-
stood that ˆV represents a class. We extend the assignment of Boolean values to
sentences of this augmented language by putting, for x ∈V (B),
[PDF-GLYPH-U+0001]x ∈ˆV [PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
y∈V
[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002].
Thus ˆV represents the class of all standard objects in V (B). One can now show
that
V (B) |= ˆV is a transitive model of ZFC containing all the ordinals.
Moreover
V (B) |= ( ˆB is a complete Boolean algebra )( ˆV ).
So, working inside V (B), we can construct the ˆB-extension ˆV ( ˆ
B) of ˆV . Upon
interpreting Theorem 4.21 in V (B), with ˆV playing the role of M, we see that
V (B) |= U∗is a ˆV —generic ultrafilter in ˆB.
Accordingly, in V (B) we can form the quotient ˆV ( ˆ
B)/U∗and its transitive
collapse ˆV [U∗].
Applying Theorem 4.22 within V (B) (with ˆV playing the role of M and ˆB
that of B) we have
V (B) |= ˆV [U∗] is the model of ZFC generated by U∗and ˆV .
Also, using Theorem 4.22 and Problem 4.26 one can show that, for any countable
transitive ∈-model M of ZFC, the statement
V (B) |= ∀x(x ∈ˆV [U∗])
(∗)
holds in M. Moreover, in order to derive (∗) in M, one only requires the conjunc-
tion of a finite number of axioms of ZFC to hold there. Hence, by the remarks
following Lemma 4.25, (∗) holds in the real world (i.e. V ) for every complete

```

## PDF page 121 | printed page 101

```text
GENERIC ULTRAFILTERS AND MODELS OF ZFC
101
Boolean algebra B. Therefore, if we identify ˆV with V , we may regard V (B) as
the Boolean-valued model of ZFC generated by U∗and V , or as the Boolean-
valued model obtained by adjoining the B-valued set U∗to V . It is precisely for
this reason that we call V (B) a Boolean extension of V .
Problems
Throughout, M is a transitive ∈-model of ZFC and B is a complete Boolean
algebra in the sense of M.
4.26 (Truth in M (B)) Suppose that M is countable, let φ(v1, . . . , vn) be a
formula and let x1, . . . , xn ∈M (B). Show that M (B) |= φ(x1, . . . , xn) iffM[U] |=
φ[iU(x1), . . . , iU(xn)] for every M-generic ultrafilter U, where iU is the canonical
map of M (B) onto M[U]. (Use Theorem 4.23 and Lemma 4.11.) Hence obtain a
new proof of Theorem 4.21. (Use Lemma 4.25.)
4.27 (Countably M-complete ultrafilters) An ultrafilter U in B is said to
be countably M-complete if whenever X ∈P (M)(B) is countable in M, we have
[PDF-GLYPH-U+0004]
X ∈U ↔X ∩U ̸= ∅.
Put N = M (B)/U. Show that the following are equivalent:
(i) U is countably M-complete;
(ii) ω(N) is well-ordered under ∈U;
(iii) ω(N) = {ˆnU : n ∈ω}.
(For (i) →(iii), argue as in Theorem 4.6. For (ii) →(i), assume (i) fails, choose
a partition of unity {am : m ∈ω} ∈M with am /∈U for all m ∈ω; using the
Mixing Lemma define sn = Σm>nam · (m −n)[PDF-GLYPH-U+0001] for each n ∈ω. Now show that
{sU
n : n ∈ω} is a descending sequence of members of ω(N).)
4.28 (Atoms in B) Let a be an atom in B, i.e. such that a ̸= 0 and, for any
x ∈B, x ≤a →x = 0 or x = a.
(i) Show that the set Ua = {x ∈B : a ≤x} is an ultrafilter in B (called the
ultrafilter generated by a).
(ii) Show that Ua is M-generic, and that Ua ∈M. Deduce that M[Ua] = M.
(iii) Let U be an ultrafilter in B such that U ∈M, and put a = [PDF-GLYPH-U+0002] U. Show
that the following are equivalent: (a) a ̸= 0, (b) a is an atom, (c) U = Ua.
4.29 (Atoms and M[U]) Let A be the set of all atoms in B, and let U∗be the
canonical generic ultrafilter in M (B).
(i) Show that [PDF-GLYPH-U+0003]
y∈M[PDF-GLYPH-U+0001]U∗= ˆy[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0003] A. (Observe that [PDF-GLYPH-U+0001]U∗= ˆy[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]ˆy
is an
ultrafilter in
ˆB[PDF-GLYPH-U+0002] = 0 or 1, and use Problem 4.28 (iii).)

```

## PDF page 122 | printed page 102

```text
102
GENERIC ULTRAFILTERS AND MODELS OF ZFC
(ii) Show that [PDF-GLYPH-U+0002]
x∈M (B)
[PDF-GLYPH-U+0003]
y∈M[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0003] A. (For any atom a ∈B,
and any x ∈M (B), show, using Problem 4.28(i) and Lemma 4.11 that
a ≤[PDF-GLYPH-U+0003]
y∈M[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002].)
(iii) Assume that M |= V = L. Show that
[PDF-GLYPH-U+0001]V = L[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0006]
x∈M (B)
[PDF-GLYPH-U+0004]
y∈M
[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
y∈M
[PDF-GLYPH-U+0001]U∗= ˆy[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]L(U∗)[PDF-GLYPH-U+0002].
(Use Theorem 1.46 and (i).)
(iv) Put η = 1 if M |= V = L and η = 0 if M |= V ̸= L. Show that
[PDF-GLYPH-U+0001]V = L[PDF-GLYPH-U+0002] = η ∧[PDF-GLYPH-U+0003] A.
(v) Assume that M |= V = L, and let U be an M-generic ultrafilter in B.
Show that M[U] |= V = L iffU = Ua for some atom a ∈B. (Use (iv).)
4.30 (A trivial Boolean extension) Let u ∈M, and put B = P (M)(u). B is
then the power set Boolean algebra of u in M.
(i) Show that, for any formula φ(v1, . . . , vn), and any x1, . . . , xn ∈M,
M |= φ[x1, . . . , xn] ↔M (B) |= φ(ˆx1, . . . , ˆxn).
(If [PDF-GLYPH-U+0001]φ(ˆx1, . . . , ˆxn)[PDF-GLYPH-U+0002] ̸= 1, let a be an atom ≤[PDF-GLYPH-U+0001]¬φ(ˆx1, . . . , ˆxn)[PDF-GLYPH-U+0002] and use
Problem 4.28 (ii).)
(ii) Let U be any ultrafilter in B. Show that, for any sentence σ,
M |= σ ↔M (B)/U |= σ.
4.31 (A transitive model of ¬AC) Let G ∈M be a group acting on B, and
let Γ ∈M be a filter of subgroups of G. Put M (Γ) = (V (Γ))(M) (for the definition
of V (Γ), see Chapter 3). Let U be an M-generic ultrafilter in B. Recalling that
i is the natural map of M (B), onto M[U], put M[Γ, U] = ⟨i[M (Γ)], ∈|i[M (Γ)]⟩.
(i) Show that M ⊆M[Γ, U], and that M[Γ, U] is transitive.
(ii) Show that, for any formula φ(v1, . . . , vn), and any x1, . . . , xn ∈M (Γ),
M[Γ, U] |= φ[i(x1), . . . , i(xn)] ↔[PDF-GLYPH-U+0001]φ(x1, . . . , xn)[PDF-GLYPH-U+0002]Γ ∈U.
(iii) Show that, if M is countable, then for a suitable choice of B, Γ and
U, M[Γ, U] is a countable transitive model of ZF in which AC fails.
(Use Theorem 3.21)
4.32 (The converse to Corollary 4.7 fails)2 Suppose that there is a meas-
urable cardinal µ > ω and an inaccessible cardinal κ > µ. Then it follows
2This problem assumes an acquaintance with measurable cardinals; cf. Drake (1974).

```

## PDF page 123 | printed page 103

```text
GENERIC ULTRAFILTERS AND MODELS OF ZFC
103
that M = ⟨Rκ, ∈|Rκ⟩is a transitive ∈-model of ZFC. Let U be a µ-complete
nonprincipal ultrafilter in Pµ ∈M. Show that M (P µ)/U is well-founded but U
is not M-generic. (Note that, by Problem 3.13, M (P µ)/U is isomorphic to the
ultrapower M µ/U.)
4.33 (Construction of uncountable transitive models of ZFC+V ̸= L)
(i) Let κ be an infinite cardinal, and suppose that the complete Boolean
algebra B contains a κ-closed dense subset P (Problem 2.17). Show that,
for any S ⊆PB such that |S| ≤κ, there is an S-complete ultrafilter in
B. (Let S = {Tξ : ξ < κ} and first confine attention to the case in which
[PDF-GLYPH-U+0003] Tξ = 1 for all ξ < κ. Let J be a sufficiently large index set so that
each Tα can be enumerated as {tξj : j ∈J}. Using the fact that P is
κ-closed, construct by transfinite recursion a function f ∈Jκ such that
[PDF-GLYPH-U+0002]
ξ<α tξf(ξ) ̸= 0 for each α < κ. Conclude that there is an ultrafilter which
intersects each Tξ; now apply this to the general case.)
(ii) Let κ be a regular cardinal. Show that, for each family S of subsets
of Bκ(κ, 2) (Problem 2.18) such that |S| ≤κ, there is an S-complete
ultrafilter in Bκ(κ, 2). (Use (i) and Problem 2.18(ii).)
(iii) Suppose that there exists an inaccessible cardinal λ > ω. Show that,
for each infinite cardinal κ
<
λ there is a transitive ∈-model of
ZFC + V
̸= L of cardinality κ. (By L¨owenheim–Skolem it is enough
to prove the result for all regular κ < λ. So let κ be regular, put
B = Bκ(κ, 2) and M = ⟨Rλ, ∈| Rλ⟩. Using the Maximum Principle
in M (B), for each formula φ(v0, . . . , vn) let fφ: (M (B))n →M (B) be a
‘Skolem function for φ in M (B)’, that is, such that, for all x1, . . . , xn ∈
M (B), [PDF-GLYPH-U+0001]∃v0φ(v0, x1, . . . , xn)[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]φ(fφ(x1, . . . , xn), x1, . . . , xn)[PDF-GLYPH-U+0002]. Let A be
the closure of the set {ˆξ : ξ < κ} under all the fφ. By (ii), let U be an S-
complete ultrafilter in B, where S = {{[PDF-GLYPH-U+0001]a = ˆξ[PDF-GLYPH-U+0002] : ξ < κ}: a ∈A}. Show that
the structure ⟨{aU : a ∈A}, ∈U⟩is a well-founded model of ZFC+V ̸= L of
cardinality κ.)
4.34 (Generic sets of conditions) Let ⟨P, ≤⟩be a partially ordered set in M.
A subset X of P is said to be dense in P if ∀y ∈P∃x ∈X[x ≤y], and dense
below an element p ∈P if ∀y ≤p∃x ∈X[x ≤y]. A subset G of P is said to be
M-generic if
(a) x ∈G, y ∈P, x ≤y →y ∈G;
(b) ∀xy ∈G∃z ∈G[z ≤x ∧z ≤y];
(c) G [PDF-GLYPH-U+001C] X ̸= ∅for every dense subset X of P, which is in M.
(i) Show that, if G is M-generic in P and X ⊆P is dense below an element
of G, then X [PDF-GLYPH-U+001C] G ̸= ∅.
Now let Q be the refined associate of P (Problem 2.4) and let j : P →Q
be the canonical map (if P is refined then P = Q and j is the identity).

```

## PDF page 124 | printed page 104

```text
104
GENERIC ULTRAFILTERS AND MODELS OF ZFC
Let B = RO(Q)(M) be the Boolean completion of Q in M, and identify Q as
a dense subset of B.
(ii) Show that, if G is M-generic in P, then
G = {x ∈B : ∃y ∈G[j(y) ≤x]}
is an M-generic ultrafilter (called the M-generic ultrafilter generated by
G). Show also that G = j−1[G]. Show conversely, that, if U is an M-generic
ultrafilter in B, then j−1[U] is an M-generic subset of P. Deduce that, if
M is countable, P has an M-generic subset.
It follows from (ii) that, if U is the M-generic ultrafilter generated by an
M-generic subset G of P, then G is definable from U and vice-versa. Under these
circumstances we write M[G] for M[U]. If p ∈P, and σ is an L(B)
M -sentence, we
write p ⊩σ for j(p) ⊩σ.
(iii) Show that, if G is M-generic in P, M[G] is the least transitive model of
ZF, which includes M and contains G.
(iv) Let G be M-generic in P and let i be the canonical map of M (B) onto
M[G]. Show that, for any formula φ(v1, . . . , vn) and any x1, . . . , xn ∈M (B),
M[G] |= φ[i(x1), . . . , i(xn)] ↔∃p ∈G[p ⊩φ(x1, . . . , xn)].
(v) Iteration lemma. Let P be a refined partially ordered set in M, let G
be an M-generic subset of P, let Q be a refined partially ordered set in
M[G], and let H be an M[G]-generic subset of Q. Show that there is
a refined partially ordered set R in M and an M-generic subset K of
R such that M[G][H] = M[K]. (Let ≤Q be the partial ordering of Q.
First show that without loss of generality we may assume that Q (but not
≤Q) is in M. Let B be the Boolean completion of P in M, let i be the
canonical map of M (B) onto M[G], let ≤∗be an element of M (B) such
that i(≤∗) = ≤Q, and let σ be the L(B)
M -sentence: ⟨ˆQ, ≤∗⟩is a refined
partially ordered set. Observe that there is p ∈G for which p ⊩σ. Now
let P ′ = {p ∈P : p ⊩σ}, R = P ′ × Q and define the relation ≤on R by
⟨p1, q1⟩≤⟨p2, q2⟩iff(p1 ≤p2 and p1 ⊩ˆq1 ≤∗ˆq2). Show that ⟨R, ≤⟩is a
refined partially ordered set in M. Now put G′ = G∩P ′ and K = G′ ×H.
Show that every dense subset of P ′ meets G′; use this, together with the
genericity of G and H to prove that K is M-generic. Finally, use the fact
that G = {p ∈P : ∃r ∈G′[r ≤p]} to prove the last assertion.)
(vi) Product lemma. Let P and Q be refined partially ordered sets in M, let
G be an M-generic subset of P and let H be an M[G]-generic subset of
Q. Give P × Q the product ordering: ⟨p1, q1⟩≤⟨p2, q2⟩iffp1 ≤p2 and
q1 ≤q2. Show that G × H is an M-generic subset of P × Q and that
M[G × H] = M[G][H]. (Like (v).)

```

## PDF page 125 | printed page 105

```text
GENERIC ULTRAFILTERS AND MODELS OF ZFC
105
4.35 (Canonical generic sets and the adjunction of maps) Let P be a
basis for B in M. Define G∗∈M (B) by dom(G∗) = {ˆp : p ∈P}, G∗(ˆp) = p for
p ∈P.
(i) Let G be M-generic in P, and let i : M (B) →M[G] be the canonical map.
Show that i(G∗) = G. (Like Theorem 4.19.)
(ii) Show that
M (B) |= G∗is a generic subset of ˆP.
(Like Theorem 4.21.) For this reason G∗is called the canonical generic set
in M (B).
Now define G∗∗∈M (B) by dom(G∗∗) = [PDF-GLYPH-U+0015]{dom(y) : y ∈dom(G∗)} and
G∗∗(x) = [PDF-GLYPH-U+0001]∃y ∈G∗[x ∈y] [PDF-GLYPH-U+0002] for x ∈dom(G∗∗).
(iii) Show that M (B) |= G∗∗= [PDF-GLYPH-U+0015] G∗
Now suppose that a, b are nonempty elements of M such that |b| ≥2 and
ℵ0 ≤|a| in M. Let G be an M-generic subset of P = C(a, b)(M) and let B =
RO(ba)(M).
(iv) Show that M (B)
|= G∗∗is a map of
ˆa onto ˆb. (See the proof of
Theorem 5.1.)
(v) Show that M[G] |= [PDF-GLYPH-U+0015] G is a map of a onto b.
Results (iv) and (v) show that, for this choice of B and G, in M (B) we have
adjoined the canonical ‘map’ G∗∗of ˆa onto ˆb and in M[G] we have adjoined
the map [PDF-GLYPH-U+0015] G of a onto b. Notice that if a is (really) countable and b is (really)
uncountable, no transitive model of ZF can contain a map of a onto b. It follows
that, if M is uncountable, there may be no M-generic subset of C(a, b)(M) and
hence no M-generic ultrafilters in RO(ba)(M). On the other hand,
(vi) If M is countable, show that there is an M-generic subset of P. (Use
Theorem 4.23 and Problem 4.34(ii).)
(vii) Let M be countable, put P = C(ω, 2)(M) and let G be an M-generic subset
of P. Show that, in M[G], [PDF-GLYPH-U+0015] G is a nonconstructible map of ω into 2. (Like
Theorem 2.6.)
(viii) Let M be countable, and suppose that M |= GCH. Put P = C(ω ×
ω2, 2)(M) and let G be an M-generic subset of P. Show that, in M[G], [PDF-GLYPH-U+0015] G
is a map of ω × ω(M)
2
onto 2. For each ν < ω(M)
2
, put uν = {n ∈ω :
([PDF-GLYPH-U+0015] G)(n, ω) = 1}. Show that {uν : ν < ω(M)
2
} is a set of ℵ(M)
2
= ℵ(M[G])
2
subsets of ω in M[G]. (Like Theorem 2.12.)
4.36 (Adjunction of a subset of ω) Let P be a basis for B in M, and let G
be an M-generic subset of P. If s ∈M[G], s ⊆m (or equivalently, if s ∈M[U],
s ⊆M where U is the M-generic ultrafilter generated by G, cf. Problem 4.34),

```

## PDF page 126 | printed page 106

```text
106
GENERIC ULTRAFILTERS AND MODELS OF ZFC
it can be shown—although we do not prove it here (for a proof see Grigorieff
1975)—that there is a least transitive model M[s] of ZF, which includes M ∪{s}.
M[s] is called the model of ZF obtained by adjoining s to M: it has the following
basic properties:
(1) M[s] ⊆M[G];
(2) M[s] |= AC;
(3) if t ∈M[G] is absolutely definable from s and elements of M, then t ∈
M[s].
(i) Let a, b ∈M; let G be an M-generic subset of C(a, b)(M) and
let F
= [PDF-GLYPH-U+0015] G. Show that M[F] = M[G]. (Note that we have
G = {f ∈C(a, b)(M) : f ⊆F}.)
(ii) Let κ be an infinite cardinal in M; let G be a generic subset of
C(ω, κ)(M), and let F = [PDF-GLYPH-U+0015] G. Show that there is s ⊆ω, s ∈M[F]
such that M[F] = M[s]. (Put s = {2n3m : F(n) ≤F(m)} ∈M[F]. Put
m ∼n iffF(m) = F(n); the set A of equivalence classes ˜m can be
ordered by ˜m < ˜n iff2n3m /∈s. Show that F induces an order preserving
map F ′ : ⟨A, <⟩→⟨κ, <⟩, so that ⟨A, <⟩is well-ordered in M[s]. Let
F ′′ : A →α be an isomorphism of A with an ordinal in M[s]. Show
that F ′′ ◦(F ′)−1 is the identity, and conclude that F ∈M[s].)
4.37 (Intermediate submodels and complete subalgebras) Let X ∈
P (M)(B). The complete subalgebra (in M) of B generated by X is defined to be
the least complete subalgebra of B in M which includes X.
(i) Suppose that |B| = κ (in M), and let B′ be the complete subalgebra of B
generated by X. Define the sets {Bα : α < κ+(M)} inductively as follows:
B0 = X; if α is odd, Bα = {b∗: b ∈[PDF-GLYPH-U+0015]
β<α Bβ}; if α is even, Bα = {[PDF-GLYPH-U+0003] X :
X ∈M and X ⊆[PDF-GLYPH-U+0015]
β<α Bβ}; if α is a limit, Bα = [PDF-GLYPH-U+0015]
β<α Bβ. Show that
B′ = [PDF-GLYPH-U+0015]
β<α Bβ.
From now on we let U be an M-generic ultrafilter in B, let i : M (B) →M[U] be
the canonical map.
(ii) Let s ∈M[U] and s ⊆M. Show that there is t ∈M such that s ⊆t,
and hence s∗∈M (B) such that i(s∗) = s and dom(s∗) = t. (For each
x ∈M[U] let x ∈M (B) be such that i(x) = x. Then s ⊆M means
that [PDF-GLYPH-U+0003]
y∈M[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002] ∈U for each x ∈s. Now argue as in the proof of
Lemma 1.36. For the second assertion, consult the proof of Lemma 1.38.)
(iii) Let s ∈M[U] and s ⊆M. Let B(s∗) be the complete subalgebra of B
generated by {[PDF-GLYPH-U+0001]ˆx ∈s∗[PDF-GLYPH-U+0002] : x ∈M}, where s∗is as in (ii). Show that M[s] =
M[U ∩B(s∗)]. (Notice first that the equation in question makes sense
because U ∩B(s∗) is an M-generic ultrafilter in B(s∗) and s∗∈M (B(s∗)).
Next, show that s ∈M[U ∩B(s∗)], so that M[s] ⊆M[U ∩B(s∗)]. Now
prove the reverse inclusion by showing that, if N is any transitive model of
ZF and M ∪{s} ⊆N, then U ∩B(s∗) ∈N. Put Uα = U ∩Bα, where the Bα

```

## PDF page 127 | printed page 107

```text
GENERIC ULTRAFILTERS AND MODELS OF ZFC
107
are defined as in (i), with X = {[PDF-GLYPH-U+0001]ˆx ∈s∗[PDF-GLYPH-U+0002] : x ∈M}. Show by induction that
Uα ∈N for all α < (|B|+)(M). Conclude that U ∩B(s∗) = [PDF-GLYPH-U+0015]
α Bα ∈N.)
(iv) Let N be a transitive model of ZFC such that M ⊆N ⊆M[U]. Show
that N = [PDF-GLYPH-U+0015]{M[s] : s ⊆Mand s ∈N}. (Given x ∈N, show that there is
s ∈N with s ⊆ORD(N) = ORD(M) such that x ∈M[s] as follows. Since
AC holds in N, there is a bijection f in N of a cardinal κ ∈N onto the
transitive closure t of x. Define r ⊆κ × κ by ⟨α, β⟩∈r ↔f(α) ∈f(β).
Let g be the canonical map of κ × κ onto κ (in M), and put s = g[r].)
(v) Let N be a transitive model of ZFC such that M ⊆N ⊆M[U]. Show that
there is a complete subalgebra A of B such that N = M[U ∩A]. (By (iv),
choose s ⊆M, s ∈N such that P (N)(B) ∈M[s] ⊆N. Now use (iii) and
(iv) to get N = M[s] and apply (iii) again.)
(vi) B is said to be countably generated (in M) if there is a countable subset
X of B in M such that the complete subalgebra of B generated by X is B
itself. Show that, if B is countably generated, then there is an s ∈M[U],
s ⊆ω such that M[U] = M[s]. (Let X = {bn : n ∈ω} be the countable
generating set. Define s′ ∈M (B) by dom(s′) = ˆω and s′(ˆn) = bn. Use (iii)
to show that s = i(s′) meets the requirements.)
4.38 (Involutions and generic ultrafilters) Let U be an M-generic ultrafil-
ter in B and let π ∈M be an automorphism of B.
(i) Show that π[U] is an M-generic ultrafilter in B and that M[U] = M[π[U]].
(ii) Let f : B →B, f ∈M be such that f[U] ⊆U. Show that there is a b ∈U
such that f(x) ≥x for all x ≤b. (Put b = [PDF-GLYPH-U+0002]{x∗∨f(x) : x ∈B}.)
(iii) An M-involution of B is an automorphism π ∈M of B such that π2 is
the identity. Let W ⊆B, W ∈M[U]. Show that the following conditions
are equivalent:
(a) W is an M-generic ultrafilter in B and M[U] = M[W];
(b) there is an M-involution π of B such that π[U] = W. (For (b) →(a),
use (i). For (a) →(b), assume (a) and U ̸= W. Let iU, iW be
the canonical maps of M (B) onto M[U], M[W] respectively and let
U, W be such that iw(U) = U, iU(W) = W. Define the functions
k, l, m, n of B into B by k(x) = [PDF-GLYPH-U+0001]ˆx ∈U[PDF-GLYPH-U+0002], m(x) = [PDF-GLYPH-U+0001]ˆx ∈W[PDF-GLYPH-U+0002], l(x) =
[PDF-GLYPH-U+0002]{y ∈B : x ≤m(y)}, n(x) = [PDF-GLYPH-U+0002]{y ∈B : x ≤k(y)}. Now put
f(x) = k(x) ∧l(x), g(x) = m(x) ∧n(x). Show that (g ◦f)[U] ⊆U and
(f ◦g)[W] ⊆W and that (g ◦f)(x) ≤x, (f ◦g)(x) ≤x. By (ii),
choose b0 ∈U, c0 ∈W such that (g ◦f)(x) = x for all x ≤b0 and
(f ◦g)(x) = x for all x ≤c0. Since U ̸= W, we may assume that
b0 ∧c0 = 0. Put b = b0 ∧g(c0) ∈U and c = f(b) ∈W, and let
Bb = {x ∈B : x ≤b}, Bc = {x ∈B : x ≤c}. Show that f|Bb is an
isomorphism of Bb onto Bc and g|Bc is the inverse of f|Bb. Now put,
for x ∈B, π(x) = f(x ∧b) ∨g(x ∧c) ∨(x −(b ∧c)).)

```

## PDF page 128 | printed page 108

```text
108
GENERIC ULTRAFILTERS AND MODELS OF ZFC
4.39 (The submodel of hereditarily ordinal definable sets) Let LS be
the extension of the language L of set theory to include a new unary predicate
symbol S, and let L(B)
S
be the language obtained for L(B)
M
by adding S. We
extend the assignment of Boolean values to L(B)
S
-sentences by defining, for x ∈
M (B), [PDF-GLYPH-U+0001]S(x)[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0003]
y∈M[PDF-GLYPH-U+0001]x = ˆy[PDF-GLYPH-U+0002]. Let U be an M-generic ultrafilter in B, and
let iU be the canonical map of M (B) onto M[U]. We write (M[U], M) for the
LS-structure obtained from M[U] by interpreting S as the subset M of M[U].
(i) Show that for any LS-formula φ(v1, . . . , vn) and any x1, . . . , xn ∈M (B)
(M[U], M) |= φ[iU(xi), . . . , iU(xn)] ↔[PDF-GLYPH-U+0001]φ(x1, . . . , xn)[PDF-GLYPH-U+0002] ∈U.
Now put (ODM)M[U] for the collection of all elements of M[U] which are
definable in (M[U], M) from (ordinals and) elements of M, (HODM)M[U] for
the collection of all elements of (ODM)M[U] whose transitive closure is in
(ODM)M[U]. (ODM)M[U] and (HODM)M[U] are the sets of elements of M[U]
which are ordinal definable, and hereditarily ordinal definable, respectively, from
M in M[U]. It can be shown that (HODM)M[U] is a transitive model of ZFC;
evidently M ⊆(HODM)M[U] ⊆M[U], so by Problem 4.37(v) there is a com-
plete subalgebra A of B such that (HODM)M[U] = M[U ∩A]. We now describe
A explicitly.
Let B+ = {x ∈B : π(x) = x for every automorphism π ∈M of B}. It is
easy to see that B+ is a complete subalgebra of B.
(ii) Show that (HODM)M[U] = M[U ∩B+]. (Put X = {W ∈M[U] : W
is an M-generic ultrafilter in B and M[U] = M[W]}. By Problem 4.38
X = {π[U] : π ∈M is an automorphism of B}. Hence show that U ∩B+ =
[PDF-GLYPH-U+001C]{W ∩B+ : W ∈X} and that U ∩B+ is definable in (M[U], M) from B.
Infer that U ∩B+ ∈(HODM)M[U], so that M[U ∩B+] ⊆(HODM)M[U].
To establish the reverse inclusion, obeserve that it suffices to show that,
if s ∈(HODM)M[U] and s ⊆M[U ∩B+], then s ∈M[U ∩B+] (for if
(HODM)M[U] −M[U ∩B+] ̸= ∅, an element of it of minimal rank would
be a subset of M[U ∩B+]). Since U ∩B+ is definable in (M[U], M) from
B, so is the canonical map of M (B+) onto M[U ∩B+], so we may suppose
that s ⊆M. Let t ∈M be such that s ⊆t, let x0, . . . , xn ∈M and let
φ(v0, . . . , vn+1) be an Ls-formula such that for all x ∈t,
x ∈s ↔(M[U], M) |= φ(x, x0, . . . , xn).
Notice that [PDF-GLYPH-U+0001]φ(ˆx, ˆx0, . . . , ˆxn)[PDF-GLYPH-U+0002]
∈
B+,
and that x
∈
s if and only if
[PDF-GLYPH-U+0001]φ(ˆx, ˆx0, . . . , ˆxn)[PDF-GLYPH-U+0002] ∈U ∩B+. Conclude that s ∈M[U ∩B+].)

```

## PDF page 129 | printed page 109

```text
5
CARDINAL COLLAPSING, BOOLEAN
ISOMORPHISM, AND APPLICATIONS TO THE
THEORY OF BOOLEAN ALGEBRAS
Cardinal collapsing
We have seen in Chapter 1 that if the complete Boolean algebra B satisfies the
countable chain condition, then cardinals in V retain their true size in V (B).
In this section we show that, if B does not satisfy this condition, it becomes
possible for two infinite cardinals κ < λ to satisfy V (B) |= |ˆλ| = |ˆκ|. In this
event we say that λ has been collapsed to κ in V (B). We begin by formulating a
necessary and sufficient condition on B for this to happen.
Theorem 5.1 Let κ and λ be infinite cardinals with κ ≤λ. Then the following
conditions are equivalent :
(i) V (B) |= |ˆκ| = |ˆλ|;
(ii) there is a double sequence {bξη : ξ < κ, η < λ} ⊆B such that [PDF-GLYPH-U+0003]
ξ<κ bξη = 1
for all η < λ and {bξη : η < λ} is an antichain for each ξ < κ.
Proof (i) →(ii). Suppose (i) holds. Then we have
V (B) |= ∃f[f is a map of ˆκ onto ˆλ].
Using the Maximum Principle, it follows that there is f ∈V (B) such that
V (B) |= f is a map of ˆκ onto ˆλ.
(1)
Put bξη = [PDF-GLYPH-U+0001]f(ˆξ) = ˆη[PDF-GLYPH-U+0002] for ξ < κ, η < λ. Then if η, η′ < λ and η ̸= η′,
bξη ∧bξη′ = [PDF-GLYPH-U+0001]f(ˆξ) = ˆη ∧f(ˆξ) = ˆη′[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]ˆη = ˆη′[PDF-GLYPH-U+0002] = 0,
and, for η < λ,
[PDF-GLYPH-U+0004]
ξ<κ
bξη =
[PDF-GLYPH-U+0004]
ξ<κ
[PDF-GLYPH-U+0001]f(ˆξ) = ˆη[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]∃x ∈ˆκ[f(x) = ˆη] [PDF-GLYPH-U+0002] = 1,
by (1). Thus {bξη : ξ < κ, η < λ} satisfies (ii).

```

## PDF page 130 | printed page 110

```text
110
CARDINAL COLLAPSING
(ii) →(i). Assume (ii). Since κ < λ, we have V (B) |= |ˆκ| ≤|ˆλ|, so it suffices
to show that V (B) |= |ˆλ| ≤|ˆκ|. To this end, define f ∈V (B) by
dom(f) = {⟨ˆξ, ˆη⟩}(B) : ξ < κ, η < λ}
and, for ξ < κ, η < λ,
f(⟨ˆξ, ˆη⟩(B)) = bξη.
Using the assumption that {bξη : η < λ} is an antichain for each ξ < κ, it follows
easily that
V (B) |= f is a map with dom(f) ⊆ˆκ and ran(f) ⊆ˆλ.
Also, for each η < λ we have, by assumption,
[PDF-GLYPH-U+0001]∃x ∈ˆκ[f(x) = ˆη] [PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
ξ<κ
[PDF-GLYPH-U+0001]f(ˆξ) = ˆη[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
ξ<κ
bξη = 1.
It follows that V (B) |= ˆλ ⊆ran(f), and so V (B) |= |ˆλ| ≤|ˆκ|, completing
the proof.
Let λ be an infinite cardinal, let X be the product space λω, where λ is
assigned the discrete topology, and let B = RO(X). For each m ∈ω and η <
λ let bmη = {g ∈X : g(m) = η}. It is then straightforward to verify that
{bmη : m ∈ω, η < λ} is a subset of B satisfying Theorem 5.1(ii), with κ = ω.
Accordingly, that theorem gives:
Corollary 5.2 Let B = RO(λω), where λ ≥ℵ0. Then
V (B) |= ˆλ is countable.
This result shows that RO(λω) may be thought of as an algebra which adjoins
a collapsing map of ˆω onto ˆλ; accordingly RO(λω) is called the collapsing (ℵ0, λ)-
algebra. In the next section we shall show that these collapsing algebras have
other useful features.
Problems
5.3 (Pω [PDF-GLYPH-U+001C] L can be countable)
(i) Let λ ≥ℵ0 and let B be the collapsing (ℵ0, 2λ)-algebra. Show that
V (B) |= P ˆλ ∩L is countable.

```

## PDF page 131 | printed page 111

```text
CARDINAL COLLAPSING
111
(ii) Let M be a countable transitive model of ZFC + 2ℵ0 = ℵ1, put B =
(RO(ωω
1 ))(M), and let U be an M-generic ultrafilter in B. Show that
M[U] |= Pω ∩L is countable.
5.4 (More on collapsing algebras) Assume GCH. Let κ, λ be regular infinite
cardinals with κ < λ. Put B = Bκ(κ, λ) (cf. Problem 2.18).
(i) Show that V (B) |= Card(ˆα) for any cardinal α ≤κ. (Use Problems 2.20(i)
and 2.18.)
(ii) Show that V (B) |= Card(ˆα) for any cardinal α ≥λ+. (Show that
|Cκ(κ, λ)| = λ and so B satisfies the λ+ −cc. Now use Problem 1.53.)
(iii) Show that V (B) |= |ˆλ| = ˆκ. (Use Theorem 5.1.)
Bκ(κ, λ) is called the collapsing (κ, λ)-algebra: its effect is to collapse λ to κ
but not to collapse any cardinal ≤κ or ≥λ+.
5.5
(Consistency
of
CH
and
¬CH
with
the
existence
of
measurable cardinals) Let κ be a cardinal. An ultrafilter F in Pκ is said
to be nonprincipal if {a} /∈F for all α < κ, and κ-complete if whenever α < κ
and {Xξ : ξ < α} ⊆F, then [PDF-GLYPH-U+001C]
ξ<α Xξ ∈F. The cardinal κ is said to be measur-
able (cf. Drake 1974) if κ > ℵ0 and there is a nonprincipal κ-complete ultrafilter
in Pκ. It is known that, if κ is measurable, then κ is regular and 2λ < κ for
every cardinal λ < κ, that is, κ is inaccessible.
(i) Let κ be a measurable cardinal and let F be a κ-complete nonprincipal
ultrafilter in Pκ. Let B be a complete Boolean algebra with a basis P
such that |P| < κ. Define G ∈V (B) by dom(G) = Bdom(ˆκ) and, for
y ∈dom(G), G(y) = [PDF-GLYPH-U+0001]y ⊆ˆκ ∧∃x ∈ˆF[x ⊆y] [PDF-GLYPH-U+0002].
(a) Show that V (B) |= Card(ˆκ) ∧ˆκ > ℵ0. (Use Problem 1.53(iii).)
(b) Show that V (B) |= G is a nonprincipal filter in P ˆκ. (Use the fact that
[PDF-GLYPH-U+0001]u ∈G[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]u ⊆ˆκ[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0003]
x∈F [PDF-GLYPH-U+0001]ˆx ⊆u[PDF-GLYPH-U+0002].)
(c) Show that V (B) |= G is an ultrafilter in P ˆκ. (For this it suffices to
show that, for any p ∈P and u ∈V (B), p ⊩(u ∩ˆκ ∈G) ∨(ˆκ −u ∈G).
Let t = {α < κ : p ⊩ˆα ∈u}. Show that, if t ∈F, then p |= u ∩ˆκ ∈G.
On the other hand, if t /∈F, then {α < κ : p ⊮ˆα ∈u} ∈F; using the
κ-completeness of F and the fact that |P| < κ, deduce that there is
q ≤p such that q ⊩ˆκ −u ∈G. Now use Theorem 2.5(iii).)
(d) Show that V (B) |= G is ˆκ-complete. (Given α < κ, p ∈P and p ⊩f :
ˆα →G, it must be shown that p ⊩[PDF-GLYPH-U+001C]
x∈ˆα f(x) ∈G. For each ξ < α, put
tξ = {β < κ : p ⊩ˆβ ∈f(ˆξ)}. Argue as in (c) to derive a contradiction
from the assumption that tξ ̸∈F. Thus tξ ∈F for all ξ < α; show
that p ⊩([PDF-GLYPH-U+001C]
ξ<α tξ)ˆ⊆[PDF-GLYPH-U+001C]
x∈ˆα f(x), and use the κ-completeness of F.)
(e) Show that V (B) |= ˆκ is a measurable cardinal. (Use (a)–(d).)
Now let ZFM = ZFC + ‘there exists a measurable cardinal’.

```

## PDF page 132 | printed page 112

```text
112
CARDINAL COLLAPSING
(ii) Show that, if ZFM is consistent, so is ZFM + 2ℵ0 = ℵ1. (Let P =
Cω1(ω1, Pω) and let B = Bω1, (ω1, Pω). Notice that P is ℵ1-closed
(Problem 2.17), so that V (B) |= (Pω)ˆ = P ˆω. Now use Theorem 5.1 to
show that V (B) |= |(Pω)ˆ| ≤ℵ1. Conclude that V (B) |= 2ℵ0 = ℵ1, and
use (i) (e).)
(iii) Show that, if ZFM is consistent, so is ZFM + 2ℵ0 ≥ℵ2. (Use (i) (e) and
Theorem 2.12.)
Boolean isomorphism and infinitary equivalence
In the previous section we saw that for any pair of infinite sets there is a Boolean
extension of V in which they become equipollent. Introducing the idea of an
infinitary language, we shall extend this result from sets to structures.
Let A = ⟨A, R⟩and B = ⟨B, S⟩be structures of the same similarity type,
where R and S are binary relations.1 We write f : A ∼= B if f is an isomorphism
of A onto B and A ∼= B if f : A ∼= B for some f.
Now let C be a complete Boolean algebra. We write ˆA for the V (C)-structure
⟨ˆA, ˆR⟩(C). We say that A and B are C-isomorphic, written A ∼=C B if V (C) |=
ˆA ∼= ˆB; they are Boolean isomorphic, written A ∼=Bool B, if A ∼=C B for some C.
Next, let L be the first-order language appropriate for binary structures.
The infinitary language L∞ω has the same symbols as L except that we add
a variable xα for each ordinal α and allow conjunctions and disjunctions of
arbitrary sets of formulas in our formation rules; quantifiers, however, are added
just one at a time as usual. The class of sentences of L∞ω holding in a structure
is called its ∞ω-theory. Two structures A and B with the same theories are said
to be ∞ω-equivalent; in this event we write A ≡∞ω B.
The relation of ∞ω-equivalence can be characterized in terms of the concept
of partial isomorphism. A partial isomorphism between A and B is a nonempty
family P of functions such that
• for each f ∈P, we have dom(f) ⊆A, ran(f) ⊆B, and f is an isomorphism
of A ↾dom(f) to B ↾ran(f);
• if f ∈P, a ∈A, b ∈B, then there exist g, h ∈P, both extending f, such that
a ∈dom(g) and b ∈ran(h).
If P is a partial isomorphism between A and B, we write P: A ∼=part B; if
there exists such a P we write A ∼=part B and say that A and B are partially
isomorphic.
1We confine attention to binary structures here solely for the purposes of notational sim-
plicity. By complicating the symbolism the results given here go through for structures with
any number of finitary relations.

```

## PDF page 133 | printed page 113

```text
BOOLEAN ISOMORPHISM AND INFINITARY EQUIVALENCE
113
The following is proved in Dickmann (1975):
Proposition 5.6 A ≡∞ω B if and only if A ∼=part B.
We are going to show that, for structures, Boolean isomorphism and
∞ω-equivalence coincide. To do this we first formulate a necessary and sufficient
condition on a complete Boolean algebra C, similar to that of Theorem 5.1, for
two structures to be C-isomorphic.
Theorem 5.7 Let C be a complete Boolean algebra, A = ⟨A, R⟩and B = ⟨B, S⟩
binary structures. Then the following conditions are equivalent:
(i) A and B are C-isomorphic;
(ii) there exists a subset {uab : a ∈A, b ∈B} of C satisfying the conditions:
(a) [PDF-GLYPH-U+0003]
b∈B uab = 1 for each a ∈A;
(b) [PDF-GLYPH-U+0003]
a∈A uab = 1 for each b ∈B;
(c) uab ∧ua′b = 0 whenever a ̸= a′;
(d) uab ∧uab′ = 0 whenever b ̸= b′;
(e) if either (aRa′ and ¬bSb′) or (¬aRa′ and bSb′), then uab ∧uab′ = 0.
Proof (i) →(ii). Assume (i) and, using the Maximum Principle, choose f ∈V (C)
to satisfy V (C) |= f: ˆA ∼= ˆB. For a ∈A, b ∈B, define uab ∈C by uab = [PDF-GLYPH-U+0001]f(ˆa) =ˆb[PDF-GLYPH-U+0002].
As in the proof of Theorem 5.1, it is easily shown that the uab satisfy (a)–(d).
To prove (e), suppose that aRa′ and ¬bSb′. Then [PDF-GLYPH-U+0001]ˆa ˆR ˆa′[PDF-GLYPH-U+0002] = 1 and [PDF-GLYPH-U+0001]ˆb ˆS ˆb′[PDF-GLYPH-U+0002] = 0,
and, since V (C) |= f: ˆA ∼= ˆB, [PDF-GLYPH-U+0001]ˆa ˆR ˆa′[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]f(ˆa) ˆSf( ˆa′)[PDF-GLYPH-U+0002], so that [PDF-GLYPH-U+0001]f(ˆa) ˆSf( ˆa′)[PDF-GLYPH-U+0002] = 1.
It follows that
uab ∧ua′b′ = uab ∧ua′b′ ∧[PDF-GLYPH-U+0001]f(ˆa) ˆSf( ˆa′)[PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]f(ˆa) = ˆb ∧f( ˆa′) = ˆb′ ∧f( ˆa′) ˆSf( ˆa′)[PDF-GLYPH-U+0002]
≤[PDF-GLYPH-U+0001]ˆb ˆS ˆb′[PDF-GLYPH-U+0002]
= 0.
The argument in the case that ¬aRa′ and bSb′ is similar.
(ii) →(i). Assume (ii), and define f ∈V (C) by dom(f) = {⟨ˆa,ˆb⟩(C) : a ∈A,
b ∈B} and f(⟨ˆa,ˆb⟩(C)) = uab. Then uab = [PDF-GLYPH-U+0001]f(ˆa) = ˆb[PDF-GLYPH-U+0002]. Using (a)–(d) it is easy to
verify that V (C) |= f is a bijection of
ˆA and ˆB. Now suppose that aRa′; then,

```

## PDF page 134 | printed page 114

```text
114
CARDINAL COLLAPSING
using (a) and (e), and noting that bSb′ ↔[PDF-GLYPH-U+0001]ˆb ˆS ˆb′[PDF-GLYPH-U+0002] = 1, we get
1 =
[PDF-GLYPH-U+0004]
b∈B
uab ∧
[PDF-GLYPH-U+0004]
b′∈B
ua′b′ =
[PDF-GLYPH-U+0004]
b,b′∈B
bSb′
(uab ∧ua′b′)
=
[PDF-GLYPH-U+0004]
b,b′∈B
(uab ∧ua′b′ ∧[PDF-GLYPH-U+0001]ˆb ˆS ˆb′[PDF-GLYPH-U+0002])
=
[PDF-GLYPH-U+0004]
b,b′∈B
[PDF-GLYPH-U+0001]f(ˆa) = ˆb ∧f( ˆa′) = ˆb′ ∧ˆb ˆS ˆb′[PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]∃xy ∈ˆB[f(ˆa) = x ∧f( ˆa′) = y ∧x ˆSy] [PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]f(ˆa) ˆSf( ˆa′)[PDF-GLYPH-U+0002].
It follows that [PDF-GLYPH-U+0001]ˆa ˆR ˆa′[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]f(ˆa) ˆSf( ˆa′)[PDF-GLYPH-U+0002], for arbitrary a, a′ ∈A, whence
[PDF-GLYPH-U+0001]∀xy ∈A[x ˆRy →f(x) ˆSf(y)] [PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0006]
a,a′∈A
[PDF-GLYPH-U+0001]ˆa ˆR ˆa′ ⇒f(ˆa) ˆSf( ˆa′)[PDF-GLYPH-U+0002]
= 1.
Similarly, using (b) and (e), we obtain [PDF-GLYPH-U+0001]∀xy ∈A[f(x) ˆSf(y) →x ˆRy] [PDF-GLYPH-U+0002] = 1. It
follows that V (C) |= f : ˆA ∼= ˆB.
As a consequence we obtain.
Corollary 5.8 If A ∼=part B, then A ∼=Bool B.
Proof Suppose that P : A ∼=part B. Assign P the topology2 whose basic open
sets are those of the form {f ∈P: p ⊆f} for p ∈P. Let C be the regular open
algebra of P; for each a ∈A, b ∈B let Vab = {f ∈P: f(a) = b} and
Uab = {q ∈P : ∀p ⊇q∃f ∈Vab(p ⊆f)}.
Then Uab is the interior of the closure of Vab in P, and so Uab ∈C. From
the fact that P is a partial isomorphism it is now not difficult to deduce that
the Uab satisfy conditions (a)–(e) of Theorem 5.7, from which it follows that
A ∼=Bool B.
From this and Proposition 5.6 we obtain:
Corollary 5.9 If A ≡∞ω B, then A ∼=Bool B.
2This topology is the order topology (cf. Chapter 2) associated with the partial ordering
of inverse inclusion on P.

```

## PDF page 135 | printed page 115

```text
BOOLEAN ISOMORPHISM AND INFINITARY EQUIVALENCE
115
There are now two ways of proving the converse to Corollary 5.9. We can
either proceed directly, or, alternatively, prove the converse to Corollary 5.8.
and then invoke Proposition 5.6. Both approaches have points of interest.
Theorem 5.10 If A ∼=Bool B, then A ≡∞ω B.
Proof Let ϕ(y, z) be a set-theoretic formula expressing the condition:
y is a binary structure, z is a sentence of L∞ω and z holds in y.
The definition of satisfaction being recursive, there are restricted formulas
ψ(x, y, z) and θ(x, y, z) such that ϕ is equivalent in ZF both to ∃xψ and ∀xθ.
Now suppose that A ∼=Bool B; let C be a complete Boolean algebra such that
A and B are C-equivalent. Let σ be a sentence of L∞ω for which A |= σ. Then
ϕ(A, σ) holds in V , and hence there is a ∈V for which ψ(a, A, σ) holds in V . Since
ψ is restricted, it follows from Theorem 1.23(v) that V (C) |= ψ(ˆa, ˆA, ˆσ). Therefore
V (C) |= ∃xψ(x, ˆA, ˆσ), whence V (C) |= ϕ(ˆA, ˆσ). Therefore V (C) |= ϕ( ˆB, ˆσ), since
ˆA and ˆB are isomorphic in V (C) and so satisfy the same sentences. It follows
that V (C) |= ∀xθ(x, ˆB, ˆσ), and so in particular V (C) |= θ(ˆa, ˆB, ˆσ) for every
a ∈V . Since θ is restricted, we infer that θ(a, B, σ) holds in V for every a ∈V ,
that is, ∀xθ(x, B, σ) holds in V . Accordingly ϕ(B, σ) holds in V , i.e. B |= σ.
Replacing σ by ¬σ in this argument yields the reverse implication; we conclude
that A ≡∞ω B, and the theorem is proved.
Theorem 5.11 If A ∼=Bool B, then A ∼=part B.
Proof Suppose that A ∼=Bool B; then by Theorem 5.7 there is a complete
Boolean algebra C satisfying conditions (a)–(e) of that theorem. For each
0 ̸= u ∈C put
˜v = {⟨a, b⟩∈A × B : v ≤uab}.
We claim that
P = {˜v : 0 ̸= v ∈C}
is a partial isomorphism between A and B.
(1) Each ˜v ∈P is a one–one function. For if ⟨a, b⟩∈˜v and ⟨a, b′⟩∈˜v, then v ≤
uab∧uab′ = 0 if b ̸= b′ by Theorem 5.7(d); so since v ̸= 0 we must have b = b′.
Accordingly ˜v is a function. In a similar way, now using Theorem 5.7(c), we
can show that ˜v is one–one.
(2) Each ˜v ∈P is an isomorphism of its domain onto its range. For suppose
⟨a, b⟩∈˜v, ⟨a′, b′⟩∈˜v and aRa′. Then if ¬bSb′, it follows from Theorem 5.7(e)
that v ≤uab ∧ua′b′ = 0, so since v ̸= 0 we must have bSb′. Similarly, if bSb′,
we obtain aRa′.

```

## PDF page 136 | printed page 116

```text
116
CARDINAL COLLAPSING
(3) Suppose ˜v ∈P and a ∈A. By Theorem 5.7(a), we have [PDF-GLYPH-U+0003]
b∈B
uab = 1; hence
v = v ∧
[PDF-GLYPH-U+0004]
b∈B
uab =
[PDF-GLYPH-U+0004]
b∈B
v ∧uab.
Since v ̸= 0, for some b ∈B we must have w = v ∧uab ̸= 0. Then ˜w ∈P, ˜v ⊆˜w
and ⟨a, b⟩∈˜w, whence a ∈dom( ˜w).
Similarly, now using Theorem 5.7(b), we get ˜w ∈P such that ˜v ⊆˜w and
b ∈ran( ˜w).
Accordingly P is a partial isomorphism between A and B and the proof
is complete.
All this gives the promised
Theorem 5.12 A ∼=Bool B if and only if A ≡∞ω B.
Finally, let us call a class of sentences of L∞ω Boolean categorical if it has
a model and any pair of its models are Boolean isomorphic. It follows imme-
diately from Theorem 5.12 that the ∞ω-theory of any structure is Boolean
categorical.
Applications to the theory of Boolean algebras
It is a fact that any countably generated Boolean algebra is a homomorphic
image of the free Boolean algebra on countably many generators. (This algebra
may be explicitly described as the algebra of clopen subsets of the Cantor ternary
set with its usual topology.) In 1964 Gaifman and Hales (independently) showed
that the situation in respect of complete Boolean algebras is strikingly different.
Let us say that a complete Boolean algebra is countably completely gener-
ated (ccg) if there is a countable subset X of B such that the least complete
subalgebra of B, which includes X is B itself. (Under these conditions X is said
to completely generate B.) Now Gaifman and Hales showed that there are ccg
complete Boolean algebras of arbitrarily high cardinality: this implies at once
that there is no Boolean algebra B such that each ccg complete Boolean algebra
is a homomorphic image of B.
In 1965 Solovay used the properties of collapsing algebras to provide a remark-
ably simple proof of Gaifman and Hales’ theorem. Essentially, Solovay observed
that if B = RO(λω), then V (B) can be obtained by adjoining a B-valued set E of
natural numbers to V , and that the Boolean values [PDF-GLYPH-U+0001]ˆη ∈E[PDF-GLYPH-U+0002] completely generate
B: cf. Problems 4.35 and 4.36.
Theorem 5.13 Let λ be an infinite cardinal and put B = RO(λω). Then B is
ccg and |B| ≥λ. Hence there are ccg complete Boolean algebras of arbitrarily
high cardinality.

```

## PDF page 137 | printed page 117

```text
APPLICATIONS TO THE THEORY OF BOOLEAN ALGEBRAS
117
Proof Define f ∈V (B) by
dom(f) = {⟨ˆm, ˆη⟩(B) : ⟨m, n⟩∈ω × λ}
and
f( ˆm, ˆη⟩(B)) = {g ∈λω : g(m) = η}.
One can then show, as in the proof of Theorem 5.1, that f is collapsing function
from ˆω to ˆλ in V (B), that is,
V (B) |= f is a map of ˆω onto ˆλ.
(1)
Let bmη = f(⟨ˆm, ˆη⟩(B)); it is then not hard to verify that
bmη = [PDF-GLYPH-U+0001]f( ˆm) = ˆη[PDF-GLYPH-U+0002].
The bmη form a subbase for the product topology on λω, and using this fact it
is straightforward to show that the bmη completely generate B. Since there are
λ different bmη, it follows that |B| ≥λ.
Put amn = [PDF-GLYPH-U+0001]f( ˆm) < f(ˆn)[PDF-GLYPH-U+0002], for m, n ∈ω. We shall show that the amn
completely generate B, thereby proving the theorem. Since the bmη completely
generate B, it suffices to show that each bmη is in the complete subalgebra B′
of B completely generated by the amn.
We prove this last assertion by induction on η. Suppose that, for all ξ < η
and all m ∈ω we have bmξ ∈B′. We show that both [PDF-GLYPH-U+0001]f( ˆm) < ˆη[PDF-GLYPH-U+0002] and [PDF-GLYPH-U+0001]f( ˆm) ≤ˆη[PDF-GLYPH-U+0002]
are in B′, for all m ∈ω. We shall then have
bmη = [PDF-GLYPH-U+0001]f( ˆm) = ˆη[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]f( ˆm) ≤ˆη[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]f( ˆm) < ˆη[PDF-GLYPH-U+0002]∗∈B′,
completing the induction step.
First we have
[PDF-GLYPH-U+0001]f( ˆm) < ˆη[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
ξ<η
[PDF-GLYPH-U+0001]f( ˆm) = ˆξ[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
ξ<η
bmξ ∈B′,
(2)
since, by inductive hypothesis, bmξ ∈B′ for all ξ < η. And finally,
[PDF-GLYPH-U+0001]f( ˆm) ≤ˆη = [PDF-GLYPH-U+0001]∀α < f( ˆm)(α < ˆη)[PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]∀x ∈ˆω[f(x) < f( ˆm) →f(x) < ˆη][PDF-GLYPH-U+0002]
(using(1))

```

## PDF page 138 | printed page 118

```text
118
CARDINAL COLLAPSING
=
[PDF-GLYPH-U+0006]
n∈ω
[[PDF-GLYPH-U+0001]f(ˆn) < f( ˆm)[PDF-GLYPH-U+0002] ⇒[PDF-GLYPH-U+0001]f(ˆn) < ˆη[PDF-GLYPH-U+0002]]
=
[PDF-GLYPH-U+0006]
n<ω
[anm ⇒[PDF-GLYPH-U+0001]f(ˆn) < ˆη[PDF-GLYPH-U+0002] ∈B′
(by (2)).
In 1967 Kripke strengthened Solovay’s result by showing that collapsing
algebras enjoy a remarkable embedding property. If there exists a complete
monomorphism of a Boolean algebra A into B, let us say that A can be completely
embedded in B. Then Kripke’s result is:
Theorem 5.14 Let A be a Boolean algebra of infinite cardinality κ. Then A can
be completely embedded in the collapsing (ℵ0, 2κ)-algebra.
Proof Let λ = 2κ and let B = RO(λω) be the collapsing (ℵ0, λ)-algebra. We
know from Corollary 5.2 that V (B) |= ˆλ is countable, whence
V (B) |= (PA)[PDF-GLYPH-U+0001] is countable.
Let {Qξ : ξ < κ} be a partition of λ and for each ξ < κ put
bξ = {f ∈λω : f(0) ∈Qξ}.
Then the bξ form a partition of unity in B. Let {aξ : ξ < κ} be an enumeration of
A−{0A}. Then by the Mixing Lemma, there is b ∈V (B) such that bξ ≤[PDF-GLYPH-U+0001]b = ˆaξ[PDF-GLYPH-U+0002]
for all ξ < κ. It follows at once that
[PDF-GLYPH-U+0001]b ∈ˆA[PDF-GLYPH-U+0002] ≥
[PDF-GLYPH-U+0004]
ξ<κ
[PDF-GLYPH-U+0001]b = ˆaξ[PDF-GLYPH-U+0002] ≥
[PDF-GLYPH-U+0004]
ξ<κ
bξ = 1.
The predicate ‘x is a Boolean algebra’ is a restricted formula, so that
V (B) |= ˆA is a Boolean algebra.
Moreover we have, for each ξ < κ,
bξ ≤[PDF-GLYPH-U+0001]b = ˆaξ[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]b = ˆaξ[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]ˆaξ ̸= ˆ0A[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]b ̸= ˆ0A[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]b ̸= 0 ˆ
A[PDF-GLYPH-U+0002],
so that
1 =
[PDF-GLYPH-U+0004]
ξ<κ
bξ ≤[PDF-GLYPH-U+0001]b ̸= 0 ˆ
A[PDF-GLYPH-U+0002].

```

## PDF page 139 | printed page 119

```text
APPLICATIONS TO THE THEORY OF BOOLEAN ALGEBRAS
119
Let S = {X ∈PA : [PDF-GLYPH-U+0003] X exists in A}. Then V (B) |= ˆS is countable, and since
V (B) |= Rasiowa–Sikorski Lemma,
V (B) |= ∃U[U is an ˆS-complete ultrafilter in ˆA and b ∈U].
The Maximum Principle now implies the existence of a U ∈V (B) such that
V (B) |= U is an ˆS-complete ultrafilter in A and b ∈U.
(1)
We define h : A →B by
h(a) = [PDF-GLYPH-U+0001]ˆa ∈U[PDF-GLYPH-U+0002]
for a ∈A. It is easy to verify that h is a homomorphism of A into B. To see that h
is complete, observe that, if X ∈S and a = [PDF-GLYPH-U+0003] X in A, then [PDF-GLYPH-U+0001]ˆa = [PDF-GLYPH-U+0003] ˆX in ˆA[PDF-GLYPH-U+0002] = 1,
so that, using (1),
h(
[PDF-GLYPH-U+0004]
X) = h(a) = [PDF-GLYPH-U+0001]ˆa ∈U[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]
[PDF-GLYPH-U+0004] ˆX ∈U[PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]∃x ∈ˆX(x ∈U)[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
x∈X
[PDF-GLYPH-U+0001]ˆx ∈U[PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0004]
x∈X
h(x) =
[PDF-GLYPH-U+0004]
h[X].
And finally h is one–one, because if 0A ̸= a ∈A, then a = aξ for some ξ < κ,
whence h(a) = [PDF-GLYPH-U+0001]ˆaξ ∈U[PDF-GLYPH-U+0002] ≥[PDF-GLYPH-U+0001]b ∈U[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]ˆaξ = b[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]ˆaξ = b[PDF-GLYPH-U+0002] ̸= 0.
Theorems 5.13 and 5.14 immediately give
Corollary 5.15 Each Boolean algebra can be completely embedded in a ccg
complete Boolean algebra.
Problems
5.16 (Universal complete Boolean algebras) Let κ be an infinite cardinal.
A Boolean algebra B is said to be κ-universal if for each Boolean algebra A of
cardinality ≤κ there is a monomorphism of A into B. If B is complete, show
that the following conditions are equivalent:
(i) B is κ-universal;
(ii) B has an antichain of cardinality κ. (For (ii) →(i); argue as in the proof
of Theorem 5.14, ignoring the collapsing property.)
5.17 (Homogeneous Boolean algebras) Show that, for each λ, the collapsing
(ℵ0, λ)-algebra is homogeneous. Deduce that each Boolean algebra can be com-
pletely embedded in a homogeneous complete Boolean algebra. (To establish
homogeneity, argue along the lines of Lemma 3.7.)

```

## PDF page 140 | printed page 120

```text
6
ITERATED BOOLEAN EXTENSIONS, MARTIN’S AXIOM,
AND SOUSLIN’S HYPOTHESIS
Souslin’s hypothesis
It is a fact that the real line can be characterized up to order isomorphism as
the unique linearly ordered set, which is order dense, complete and unbounded,
as well as separable, that is, has a countable subset intersecting each nonempty
open interval. In 1920 Souslin raised the question as to whether separability
could be replaced by the following—apparently weaker—condition:
Every family of disjoint open intervals is countable.
(∗)
Souslin’s problem may be equivalently stated in the form of
Souslin’s hypothesis (SH) Every order dense linearly ordered set satisfying
(∗) above is separable.
To see that the two formulations are equivalent, let us write SH′ for the
assertion that any complete, unbounded, order dense, linearly ordered set satis-
fying (∗) is isomorphic to the real line R. Then clearly SH →SH′. Conversely, if
SH′ holds, let P be an (infinite) order dense linearly ordered set satisfying (∗).
Then P contains a copy of the ordered set Q of rational numbers. The (Dede-
kind) order completion C of P (with its end-points removed) is then order dense,
unbounded, and satisfies (∗) since P does. Thus SH′ implies that C is isomorphic
to R. So P may be regarded as a dense subset of R, which contains Q. Clearly
P is then separable, and SH follows.
In this chapter we are going to establish first the independence and then
the relative consistency of SH with ZFC. The first step in this process is to
introduce the notion of a tree.
A tree is a partially ordered set ⟨T, ≤T ⟩with the property that, for each
x ∈T, the set {y : y <T x} of predecessors of x is well-ordered by ≤T . For each
x ∈T, we write o(x) for the order type of {y : y <T x}; o(x) is then an ordinal.
For each ordinal α, the αth level of T consists of all x ∈T for which o(x) = α.
The height of T is the least α such that the αth level of T is empty. A branch in
T is a maximal linearly ordered subset of T. A subset X of T is said to be free
if any two different elements x, y of X are incomparable, that is, neither x ≤T y

```

## PDF page 141 | printed page 121

```text
SOUSLIN’S HYPOTHESIS
121
nor y ≤T x. Finally, a tree T is called a Souslin tree if
T has height ω1;
every branch in T is countable;
every free subset of T is countable.
We can now reformulate Souslin’s hypothesis in terms of Souslin trees.
Lemma 6.1 SH holds iffthere are no Souslin trees.
Proof Sufficiency Suppose SH fails; then there is a dense linearly ordered set P
which is not separable but in which every family of disjoint open intervals is
countable. We use P to construct a Souslin tree T as follows. T will consist of
closed (nondegenerate) intervals in P, and will be partially ordered by inverse
inclusion ⊇.
We construct T by recursion on α < ω1. Let I0 = [a0, b0] be arbitrary (with
a0 < b0). Assuming that we have got all Iβ for β < α, consider the countable
set C = {aβ : β < α} ∪{bβ : β < α} of endpoints of the intervals Iβ. Since P
is not separable, there must be an interval disjoint from C; let Iα = [aα, bα] be
one. The set T = {Iα : α < ω1} is uncountable and partially ordered by ⊇. If
α < β, then either Iα ⊇Iβ or Iα ∩Iβ = ∅. It follows that, for each α, the set
{I ∈T : I ⊇Iα} is well-ordered by ⊇and so T is a tree.
We show that T has no uncountable branches and no uncountable free sub-
sets. Clearly the height of T then cannot exceed ω1; and since every level of T
is evidently free and T is uncountable, it follows that T has height ω1.
If I, J are incomparable members of T, then they are, by construction, dis-
joint intervals of P; so any free subset of T is countable. To show T has no
uncountable branches, we observe that if b is a branch of length ω1, then the left
endpoints of the intervals I ∈b of from an increasing sequence {xα : α < ω1}
of points of P. But then the intervals (xα, xα+1), α < ω1 form an uncountable
collection of disjoint open intervals in P, contradicting assumption.
Necessity
Let T be a Souslin tree. First we remove from T all points x ∈T
such that {y ∈T : x ≤y} is countable, thus obtaining a new tree T ′. It is
easy to see that for each x ∈T ′ there exists y ∈T ′, y > x, at each greater
level < ω1. Next, we discard from T ′ all points x ∈T ′ for which there is only
one point y > x at the next level. This gives us a new tree T ′′. Finally from
T ′′ we expunge all points except those at limit levels. This yields a Souslin tree
in which each level has cardinality ℵ0. Thus, without loss of generality we may
assume that the same holds for T.
Now let P be the set of all branches in T; we order P as follows. First, we
order each level of T as in the rational numbers. Then, given b1, b2 ∈P, we put
b1 < b2 if the αth element of b1 precedes the αth element of b2 in the ordering of
Uα, where Uα is the least level at which b1 and b2 differ. Clearly this prescription
makes P linearly ordered and dense.

```

## PDF page 142 | printed page 122

```text
122
ITERATED BOOLEAN EXTENSIONS
If (a, b) is an interval in P, it is not hard to see that there is x ∈T such
that Ix ⊆(a, b), where Ix is the interval Ix = {c ∈P : x ∈c}. Moreover, if
Ix ∩Iy = ∅, then x and y are incomparable points of T. It follows that every
collection of disjoint open intervals in P is countable.
On the other hand, P is not separable. For if C is a countable set of branches
in T, let α be a countable ordinal exceeding the length of any branch in C. Then
if x is any point at level α, the interval Ix is disjoint from C.
The independence of SH
Before we begin the proof of independence of SH from ZFC, we require a
combinatorial lemma.
Lemma 6.2 Let S be an uncountable collection of finite sets. Then there is an
uncountable Z ⊆S and a finite set A such that X ∩Y = A for any distinct
elements X, Y ∈Z.
Proof Since S is uncountable, it is clear that uncountably many X ∈S have the
same cardinality. Thus we may assume that, for some n, |X| = n for all X ∈S.
The lemma is now proved by induction on n. If n = 1, the lemma is trivial. So
assume its truth for n, and let S be such that |X| = n + 1 for all X ∈S.
Case 1 Some element a belongs to uncountably many X ∈S. In this case we
obtain the required Z ⊆S by applying the inductive hypothesis to the family
{X −{a} : X ∈S ∧a ∈X}.
Case 2 Not case 1. Here we can easily construct a disjoint family Z = {Xα :
α < ω1} ⊆S by choosing inductively Xα to be a member of S disjoint from all
Xξ for ξ < α.
Now let M be any countable transitive ∈-model of ZFC. We shall show that
M has a generic extension M[G] containing a Souslin tree.
In M, let P be the set of all finite trees ⟨T, ≤T ⟩such that T ⊆ω1 and
α ≤T β →α ≤β (as ordinals). We partially order P by stipulating that:
⟨T1, ≤T1⟩⪯⟨T2, ≤T2⟩↔T1 ⊇T2∧≤T2 = ≤T1 |T2.
In the sequel we shall usually write ‘≤1’ for ‘≤T1’, etc.
A partially ordered set is said to satisfy the countable chain condition (ccc) if
every subset consisting of incompatible elements is countable. It is clear that
a partially ordered set satisfies ccc in this sense iffits Boolean completion
(cf. Problem 2.4) satisfies the ccc in the sense of Chapter 1.
Lemma 6.3 ⟨P, ⪯⟩satisfies ccc.
Proof Let S be an uncountable subset of P. Using Lemma 6.2, we obtain an
uncountable subset Z1 ⊆S and a finite set A ⊆ω1 such that, for any distinct

```

## PDF page 143 | printed page 123

```text
THE INDEPENDENCE OF SH
123
T1, T2 ∈Z1 we have T1 ∩T2 = A and ≤1 |A = ≤2|A. Now discard from Z1 all
trees T for which there exist α ∈A and β < α such that β ∈T −A. Only
countably many trees are lost from Z1 in this way. If we call what is left Z2,
then Z2 is uncountable. But now any T1, T2 ∈Z are compatible: for if we define
≤3 on T3 = T1 ∪T2 by
α ≤3 β ↔α ≤1 β ∨α ≤2 β,
then ⟨T3, ≤3⟩⪯⟨T1, ≤1⟩and ⟨T3, ≤3⟩⪯⟨T2, ≤2⟩. The lemma follows.
Now, using Problem 4.34, we choose an M -generic subset G of P and put
H = [PDF-GLYPH-U+0015] G. We let ≤H be the partial ordering on H induced in the obvious way
by the partial orderings of the members of G. It is easy to see that H is a tree
in M[G].
Theorem 6.4 M[G] |= H is a Souslin tree.
Proof Let us call a point x of a tree a branch point if there are at least two
points y > x at the next level above x.
We claim first that:
(1) every point of H is a branch point;
(2) for each α ∈H, the set {β ∈H : α <H β} is uncountable in M[G].
To prove (1), we take any α ∈H, choose T0 ∈G such that α ∈T0 and
observe that the set of T ∈P in which α is a branch point is dense below T0
in P. Consequently there must be T ∈G is which α is a branch point; it follows
that α is a branch point in H.
To prove (2), we again take α ∈H and T0 ∈G such that α ∈T0. Next we
observe that, for each ξ < ω(M)
1
, the set
Q = {T ∈P : α ∈T ∧∃β ∈T[ξ < β ∧α <T β]}
is dense below T0. Since G is generic, G ∩Q ̸= ∅. Hence for each ξ < ω(M)
1
there is β ∈H such that ξ < β and α <H β. But Lemma 6.3 implies that
ω(M)
1
= ω(M[G])
1
, and (2) follows.
Now we can prove the following.
(3) M[G] |= every free subset of H is countable.
For suppose (3) is false; then, for some E ∈M[G] we have
E is an uncountable free subset of H.
Let B be the Boolean completion of P, let i be the canonical map of M (B)
onto M[G], and let ˜E, ˜H ∈M (B) be such that i( ˜E) = E, i( ˜H) = H. Then, for

```

## PDF page 144 | printed page 124

```text
124
ITERATED BOOLEAN EXTENSIONS
some T0 ∈G we have
T0 || ˜E is an uncountable free subset of
˜H.
(∗)
It follows that for each ξ < ω(M)
1
we can find T ∈P and αT ∈T such that
T ⪯T0, ξ < αT and T || ˆαT ∈˜E. In this way we obtain an uncountable (in M)
set S ⊆P and, for each T ∈S an ordinal αT ∈T such that T || ˆαT ∈˜E.
Lemma 6.2 now yields an uncountable subset Z1 of S and a finite set A such
that, for any T1 ̸= T2 in Z1 we have T1 ∩T2 = A and ≤T1 |A =<T2 |A. Without
loss of generality we may assume that αT /∈A for any T ∈Z1. Since A is finite,
there must be an uncountable subset Z2 of Z such that, for any T1, T2 ∈Z2,
A ∩{β : β <T1 αT1} = A ∩{β : β <T2 αT2}.
From Z2 we discard all trees T for which there is α ∈A and β < α such that
β ∈T −A. Only countably many trees are lost in this way, so if we call what is
left Z3, then Z3 is uncountable.
If T1, T2 ∈Z3 then we have ⟨T3, ≤3⟩⪯⟨T1, ≤1⟩and ⟨T3, ≤3⟩⪯⟨T2, ≤2⟩
where T3 = T1 ∪T2 and ≤3 is defined as follows: if αT1 < αT2, then
α ≤3 β ↔α ≤1 β ∨α ≤2 β
∨[α ≤1 αT1 ∧∃γ ≤2 αT2(α ≤γ ∧γ ≤2 β)]
∨[α ≤2 αT2 ∧∃γ ≤1 αT1(α ≤γ γ ∧γ ≤1 β)]
∨[α ≤1 αT1 ∧αT2 ≤2 β],
and similarly when αT2 < αT1.
It is clear that αT1 and αT2 are comparable with respect to ≤T3. So
T3 || ˆαT1 ∈˜E ∧ˆαT2 ∈˜E ∧ˆαT1 is comparable in ˜H with ˆαT2.
But this contradicts (∗). This proves (3).
It therefore remains to prove the following.
(4) M[G] |= H has height ω1;
(5) M[G] |= every branch in H is countable.
To prove (4), we suppose that (in M[G]) H has height < ω1. Then for any
α ∈H the set {o(β) : α <H β} is countable and it follows from (2) that for some
γ < ω1 the set {β ∈H : o(β) = α} is uncountable. But this latter set is free,
contradicting (3).
Finally, suppose (5) is false; let b be a branch in H of length ω1 (in M[G]).
Using (1) we choose for each x ∈b an element f(x) ≥H
x not in b. Then
{f(x) : x ∈b} is free and uncountable in M[G], contradicting (3).
Corollary 6.5 If ZF is consistent, so are ZFC + GCH + ¬SH and ZFC+
¬CH + ¬SH.

```

## PDF page 145 | printed page 125

```text
MARTIN’S AXIOM
125
Proof Let B be the Boolean completion of P, and assume that M |= GCH. Since
P satisfies ccc, so does B and it is easily shown, using GCH in M, that M |=
|B| = 2ℵ0. It follows from Theorems 2.8 and 6.4 that M[G] |= GCH∧¬SH. Since
this holds for an arbitrary generic set G is P, we infer that M[U] |= GCH ∧¬SH
for an arbitrary generic ultrafilter U in B and hence, using Problem 4.26, that
M (B) |= GCH ∧¬SH. By the remarks following Lemma 4.25, we can transfer
this to V (B), obtaining (now under that assumption that GCH holds in V ) that
V (B) |= GCH ∧¬SH. The first assertion now follows from Theorem 1.19.
If on the other hand M |= 2ℵ0 ≥ℵ2, then M[G] |= ℵ(M)
2
≤2ℵ0. But B
satisfies ccc, and therefore, by Theorem 1.51, we have M[G] |= ℵ(M)
2
= ℵ2.
Hence M[G] |= ℵ2 ≤2ℵ0, yielding the second assertion as above.
Martin’s axiom
Having established the independence of SH from ZFC, we want now to demon-
strate its relative consistency. Rather than attempting to go about doing this
directly, however we instead formulate a principle that easily implies the nonex-
istence of Souslin trees, and give a relative consistency proof for this principle.
The principle, known as Martin’s axiom, provides an interesting alternative to
the continuum hypothesis, and has become an important tool in general topology
and infinite combinatorics.
Let κ be an infinite cardinal. Martin’s axiom at level κ is the assertion
MAκ:
If B is a Boolean algebra satisfying ccc and S is any family
of subsets of B (each member of which has a join) such that
|S| < κ, then there is an S-complete ultrafilter in B.
Notice that MAℵ1 is just a special case of the Rasiowa–Sikorski lemma, and
hence provable in ZFC. So MAκ is only novel when κ > ℵ1. We observe, however
the following.
Lemma 6.6
ZFC ⊢MAκ →κ ≤2ℵ0.
Proof Let B = RO(2ω); then B satisfies ccc. For each s ⊆ω let χs be the
characteristic function of s and let Xs = {N(p) : p ⊈χs}. It is easily verified that
[PDF-GLYPH-U+0003] Xs = 1 in B; so if MAκ with κ > 2ℵ0 there would be a {Xs : s ⊆ω}-complete
ultrafilter U in B. Now define t ⊆ω by
n ∈t ↔N({⟨n, 1⟩}) ∈U.
It is now easy to show that for any subset s ⊆ω we have t ̸= s, which is a
contradiction.

```

## PDF page 146 | printed page 126

```text
126
ITERATED BOOLEAN EXTENSIONS
Problem 6.7 (A stronger form of Martin’s axiom?) Let MAκ! be obtained
from MAκ by dropping the restriction to algebras satisfying ccc. Show that
MAκ! →κ ≤ℵ1. (Consider the collapsing (ℵ0, ℵ1)-algebra.)
We next give several alternative formulations of MAκ. If P is a partially
ordered set, and S a family of subsets of P, a subset G of P is said to be
S-generic (cf. Problem 4.34) if
(a) x ∈G, x ≤y →y ∈G;
(b) x, y ∈G →∃z ∈G[z ≤x ∧z ≤y];
(c) X ∈S ∧X dense in P →X [PDF-GLYPH-U+001C] G ̸= ∅.
Theorem 6.8 The following are equivalent for any infinite cardinal κ:
(i) MAκ.
(ii) If B is a Boolean algebra satisfying ccc with |B| < κ and S is a family of
subsets with |S| < κ, each member of which has a join, then there is an
S-complete ultrafilter in B.
(iii) If P is a partially ordered set satisfying ccc such that |P| < κ and S is a
family of subsets of P with |S| < κ, then there is an S-generic subset of P.
(iv) Same as (iii) but with ‘|S| < κ’ omitted.
Proof (i) →(ii) is trivial.
(ii)→(iii). Assume (ii) and let P be a partially ordered set satisfying ccc
with |P| < κ. Let C be the Boolean completion of P and let j : P →C be
the canonical map. Also let B be the subalgebra of C generated by j[P]. Then
|B| < κ. Now observe that if E is any family of < κ dense subsets of B, then
[PDF-GLYPH-U+0003] X = 1 in B for each X ∈E, and therefore, by (ii), there is an E-complete
ultrafilter in B. If S is any family of dense sets in P with |S| < κ, consider the
following dense subsets of B : (a) all j[X] with X ∈S; (b) all j[Zxy] for x, y ∈P,
where
Zxy = {z ∈P : [z ≤x ∧z ≤y] ∨¬Comp(z, x) ∨¬Comp(z, y)}.
Since |P| < κ, there are < κ sets of the form (a) or (b); so (ii) yields an
ultrafilter U in B which meets all of them. It is now readily verified that j−1[U]
is an S-generic subset of P.
(iii) →(iv). Assume (iii) and let P be a partially ordered set satisfying ccc.
Let S be a family of < κ dense subsets of P. For each X ∈S, let QX be a maximal
subset of X consisting of mutually incompatible elements. Since P satisfies ccc,
each QX is countable. Hence there is a subset Q of P of cardinality < κ such
that QX ⊆Q for all X ∈S and
x, y ∈Q ∧Comp(x, y) →∃z ∈Q[z ≤x ∧z ≤y].

```

## PDF page 147 | printed page 127

```text
MARTIN’S AXIOM
127
Each QX is a maximal incompatible subset of Q and, for each X ∈S, KX =
{x ∈Q : x ≤y for some y ∈QX} is dense in Q.
The partially ordered set Q is of cardinality < κ and satisfies ccc. So by (iii)
there is a {KX : X ∈S}-generic subset G of Q. It is now easily verified that the
set {x ∈P : ∃y ∈G[y ≤x]} is S-generic in P.
(iv) →(i). Assume (iv), let B be a Boolean algebra with ccc, let S be a
family of subsets of B, each member of which has a join, let P = B −{0} and
for each X ∈S let
DX = {y ∈P : ∃x ∈X[y ≤x] ∨∀x ∈X[y ∧x = 0]}.
Each DX is dense in P and so (iv) implies that there is a {DX : X ∈S}-generic
subset G of P. Clearly any ultrafilter in B extending G is S-complete.
The principle MA2ℵ0 is called Martin’s axiom and is written simply MA.
Clearly MA is a consequence of CH; but we shall see that MA can hold even when
CH fails. Moreover, we can use Theorem 6.8 to show that, in this eventuality,
Souslin’s hypothesis holds:
Theorem 6.9
MA + 2ℵ0 > ℵ1 →SH.
Proof Suppose SH is false; then there is a Souslin tree T. Let T ′ be the set of
x ∈T for which {y ∈T : x ≤T y} is uncountable. It is then easy to see that
T ′ is a Souslin tree with the property:
for each x ∈T ′there is some y > x at each greater level (< ω1).
(∗)
Now let P be the partially ordered set obtained from T ′ by reversing the
order. It is easy to see that P satisfies ccc. For each α < ω1 let
Xα = {x ∈T ′ : o(x) > α}.
Using (∗), one verifies that Xα is dense in P.
Thus, assuming MA+2ℵ0 > ℵ1, there is an {Xα : α < ω1}-generic subset G of
P. It is now a routine matter to verify that G is a branch in T ′ of cardinality ω1,
a contradiction.
It follows from Theorem 6.9 that, in order to establish the relative consistency
of SH, it suffices to establish that of MA + 2ℵ0 > ℵ1. We shall achieve this by
constructing an increasing sequence of Boolean extensions of the universe in such
a way that at each succesive stage a potential counterexample to Martin’s axiom
is ‘liquidated’ by adjoining an ultrafilter of the appropriate sort. Then, with some
finesse, we can show that the ‘limit’ of this sequence of Boolean extensions (in a

```

## PDF page 148 | printed page 128

```text
128
ITERATED BOOLEAN EXTENSIONS
sense to be made precise later on) is a Boolean-valued model of MA + 2ℵ0 > ℵ1.
We turn now to elaborating this procedure, which is called the method of iterated
Boolean extensions.
Iterated Boolean extensions
Let B be a complete Boolean algebra, and suppose we are given elements
C, ≤C of V (B) such that
V (B) |= ⟨C, ≤C⟩is a Boolean algebra.
Let A be a core for C (see Chapter 1). We shall see that A carries the structure
of a Boolean algebra in a natural way.
First we define a relation ≤A on A by putting, for each a, a′ ∈A,
a ≤A a′ ↔[PDF-GLYPH-U+0001]a ≤C a′[PDF-GLYPH-U+0002] = 1
(cf. proof of Lemma 1.43). It is easily verified that ≤A is a partial ordering on A
and that with this partial ordering A is a Boolean algebra in which the Boolean
operations ∧A, ∨A, ∗A are given by
a ∧A a′ = unique x ∈A for which [PDF-GLYPH-U+0001]x = a ∧C a′[PDF-GLYPH-U+0002] = 1;
a ∨A a′ = unique x ∈A for which [PDF-GLYPH-U+0001]x = a ∨C a′[PDF-GLYPH-U+0002] = 1;
a∗A = unique x ∈A for which [PDF-GLYPH-U+0001]x = a∗C[PDF-GLYPH-U+0002] = 1,
where ∧C, ∨C, ∗C are the Boolean operations in C (in V (B)). It is also not hard
to see that, despite the apparent freedom in the choice of the core A, the Boolean
algebra ⟨A, ≤A⟩is determined uniquely up to isomorphism. We shall write B⊗C
for A and ≤B⊗C or ≤for ≤A.
If x, y ∈B ⊗C and b ∈B, then the two-term mixture b · x + b∗· y is, with
probability 1, an element of C, and hence there is a unique element of B ⊗C
which is equal to it with probability 1. Without loss of generality we may and
shall assume in the sequel that this element of B ⊗C is b · x + b∗· y. That is, we
shall assume that B⊗C is closed under two-term mixtures of the form b · x+b∗· y.
This fact should be borne in mind when considering the next problem.
Problem 6.10 (An isomorphism of Boolean algebras) Show that the map
p : B →B ⊗ˆ2 defined by p(b) = b.ˆ1 + b∗.ˆ0 an isomorphism of Boolean algebras.
Next, we treat the computation of arbitrary joins in B ⊗C.

```

## PDF page 149 | printed page 129

```text
ITERATED BOOLEAN EXTENSIONS
129
Lemma 6.11 Let X ⊆B ⊗C and put X′ = X × {1}. Then X′ ∈V (B) and
[PDF-GLYPH-U+0001]X′ ⊆C[PDF-GLYPH-U+0002] = 1. If a ∈B ⊗C satisfies [PDF-GLYPH-U+0001]a = [PDF-GLYPH-U+0003]
C X′[PDF-GLYPH-U+0002] = 1, then a = [PDF-GLYPH-U+0003] X in B ⊗C.
Proof If x ∈X, then clearly [PDF-GLYPH-U+0001]x ∈X′[PDF-GLYPH-U+0002] = 1, so that [PDF-GLYPH-U+0001]x ≤C a[PDF-GLYPH-U+0002] = 1, whence
x ≤B⊗C a. Therefore a is an upper bound for X in B ⊗C. Also, if y ∈B ⊗C
is any upper bound for X, then [PDF-GLYPH-U+0001]x ≤C y[PDF-GLYPH-U+0002] = 1 for all x ∈X, whence
[PDF-GLYPH-U+0001]y is an upper bound forX′[PDF-GLYPH-U+0002] = 1, so that [PDF-GLYPH-U+0001]a ≤C y[PDF-GLYPH-U+0002] = 1, and therefore a ≤B⊗C y.
So a = [PDF-GLYPH-U+0003] X in B ⊗C as claimed.
As an immediate consequence we have the
Corollary 6.12 If
V (B) |= ⟨C, ≤C⟩is a complete Boolean algebra,
then B ⊗C is complete.
Next, we show that B is completely embeddable in B ⊗C. In V (B) we have
the natural monomorphism i of the two element Boolean algebra ˆ2 into C which
sends ˆ0 to 0C and ˆ1 to 1C, where 0C, 1C are the unique elements of B ⊗C which
with probability 1 are the bottom and top elements of C respectively. This in
turn induces the natural map j : B ⊗ˆ2 →B ⊗C defined by setting
j(x) = unique y ∈B ⊗C for which [PDF-GLYPH-U+0001]y = i(x)[PDF-GLYPH-U+0002] = 1.
Clearly, for x ∈B ⊗ˆ2,
[PDF-GLYPH-U+0001]x = ˆ1[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]j(x) = 1C[PDF-GLYPH-U+0002];
[PDF-GLYPH-U+0001]x = ˆ0[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]j(x) = 0C[PDF-GLYPH-U+0002],
and so j(x) can be described as the two-term mixture
j(x) = [PDF-GLYPH-U+0001]x = ˆ1[PDF-GLYPH-U+0002] · 1C + [PDF-GLYPH-U+0001]x = ˆ0[PDF-GLYPH-U+0002] · 0C
for x ∈B ⊗ˆ2. By Problem 6.10, we have a natural isomorphism p : B ∼= B ⊗ˆ2
given by p(b) = b · ˆ1 + b∗· ˆ0 for b ∈B. Thus the composite e = j ◦p is given by
e(b) = j(p(b)) = [PDF-GLYPH-U+0001]p(b) = ˆ1[PDF-GLYPH-U+0002] · 1C + [PDF-GLYPH-U+0001]p(b) = ˆ0[PDF-GLYPH-U+0002] · 0C = b · 1C + b∗· 0C.
The map e : B →B ⊗C is then given by
for b ∈B, e(b) = the unique x ∈B ⊗Cfor which
[PDF-GLYPH-U+0001]x = 1C[PDF-GLYPH-U+0002] = b, [PDF-GLYPH-U+0001]x = 0C[PDF-GLYPH-U+0002] = b∗.
(6.13)

```

## PDF page 150 | printed page 130

```text
130
ITERATED BOOLEAN EXTENSIONS
Observe that by the very definition of e we have for b ∈B
V (B) |= e(b) ∈{0C, 1C}.
(6.14)
Recall that a homomorphism h of Boolean algebras is said to be complete
if it preserves arbitrary joins, that is, if whenever X is a subset of the domain
algebra of h such that [PDF-GLYPH-U+0003] X exists, then [PDF-GLYPH-U+0003] h[X] exists in the codomain algebra
of h and is equal to h([PDF-GLYPH-U+0003] X).
Lemma 6.15 The map e is a complete monomorphism of B into B ⊗C.
Proof The fact that e is injective and preserves complements is easily established
and is left to the reader. We show that e preserves arbitrary joins in B. Suppose
then that X ⊆B. Let Y = e[X] and Y ′ = Y × {1}. Then [PDF-GLYPH-U+0001]Y ′ ⊆C[PDF-GLYPH-U+0002] = 1
and, if we choose a ∈B ⊗C to satisfy [PDF-GLYPH-U+0001]a = [PDF-GLYPH-U+0003]
C Y ′[PDF-GLYPH-U+0002] = 1, then by Lemma 6.11
we have a = [PDF-GLYPH-U+0003] Y in B ⊗C. Now (6.14) gives [PDF-GLYPH-U+0001]Y ′ ⊆{0C, 1C}[PDF-GLYPH-U+0002] = 1, so that
[PDF-GLYPH-U+0001]a ∈{0C, 1C}[PDF-GLYPH-U+0002] = 1, whence
[PDF-GLYPH-U+0001]a = 1C[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0003] [PDF-GLYPH-U+0004]
C
Y ′ = 1C ∧Y ′ ⊆{0C, 1C}
[PDF-GLYPH-U+0004]
= [PDF-GLYPH-U+0001]1C ∈Y ′[PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0004]
x∈X
[PDF-GLYPH-U+0001]e(x) = 1C[PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0004]
X.
Therefore a satisfies the defining equations (6.13) for e([PDF-GLYPH-U+0003] X) in B ⊗C; in other
words e([PDF-GLYPH-U+0003] X) = [PDF-GLYPH-U+0003] e[X]. Thus e is complete as claimed.
In view of Lemma 6.15, e is called the canonical embedding of B in B ⊗C.
We continue with some technical lemmas which we shall require later on.
Lemma 6.16 For x, y ∈B ⊗C, b ∈B, we have
b ≤[PDF-GLYPH-U+0001]x ≤C y[PDF-GLYPH-U+0002] ↔e(b) ∧x ≤B⊗C y.
Proof We have
b = [PDF-GLYPH-U+0001]e(b) = 1C[PDF-GLYPH-U+0002].
So
b ≤[PDF-GLYPH-U+0001]x ≤C y[PDF-GLYPH-U+0002] ↔V (B) |= [e(b) = 1C →x ≤C y].
(∗)

```

## PDF page 151 | printed page 131

```text
ITERATED BOOLEAN EXTENSIONS
131
But by (6.14)
V (B) |= e(b) = 1C ∨e(b) = 0C.
So
V (B) |= e(b) = 1C →x ≤C y ↔V (B) |= e(b) ∧x ≤C y
↔e(b) ∧x ≤B⊗C y.
The result now follows from (∗).
Lemma 6.17 Let X ∈V (B). Then there is Y ∈V (B) such that dom(Y ) ⊆
B ⊗C, Y is definite (1.40) and
[PDF-GLYPH-U+0001]X ⊆C[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]Y = X ∪{0C}[PDF-GLYPH-U+0002].
Proof Put b = [PDF-GLYPH-U+0001]X ⊆C[PDF-GLYPH-U+0002]. Using the Mixing Lemma, choose X′ ∈V (B) to satisfy
[PDF-GLYPH-U+0001]X′ = X ∪{0C}[PDF-GLYPH-U+0002] ≥b,
[PDF-GLYPH-U+0001]X′ = {0C}[PDF-GLYPH-U+0002] ≥b∗.
Then [PDF-GLYPH-U+0001]∅̸= X′ ⊆C[PDF-GLYPH-U+0002] = 1. Now put
Y ′ = {y ∈B ⊗C : [PDF-GLYPH-U+0001]y ∈X′[PDF-GLYPH-U+0002] = 1}
and Y = Y ′ × {1}. Notice that Y ′ is a core for X′.
We claim that Y meets the required conditions; to establish this it clearly
suffices to show that [PDF-GLYPH-U+0001]Y = X′[PDF-GLYPH-U+0002] = 1.
First, we have, for any x ∈V (B),
[PDF-GLYPH-U+0001]x ∈Y [PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
y∈Y ′
[PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002]
=
[PDF-GLYPH-U+0004]
y∈Y ′
[PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]y ∈X′[PDF-GLYPH-U+0002]
≤[PDF-GLYPH-U+0001]x ∈X′[PDF-GLYPH-U+0002],

```

## PDF page 152 | printed page 132

```text
132
ITERATED BOOLEAN EXTENSIONS
so [PDF-GLYPH-U+0001]Y ⊆X′[PDF-GLYPH-U+0002] = 1. Moreover, since [PDF-GLYPH-U+0001]X′ ̸= ∅[PDF-GLYPH-U+0002] = 1, by Lemma 1.32 there is, for
each x ∈V (B), an x′ ∈Y ′ such that [PDF-GLYPH-U+0001]x = x′[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]x ∈X′[PDF-GLYPH-U+0002]. Hence
[PDF-GLYPH-U+0001]x ∈X′[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]x = x′[PDF-GLYPH-U+0002]
≤
[PDF-GLYPH-U+0004]
y∈Y ′
[PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]x ∈Y [PDF-GLYPH-U+0002],
so [PDF-GLYPH-U+0001]X′ ⊆Y [PDF-GLYPH-U+0002] = 1. Thus the claim, and the lemma, are proved.
We recall from Problem 3.12(i) that the complete monomorphism e : B →
B ⊗C induces a natural map ¯e : V (B) →V (B⊗C). We shall identify B with its
image in B ⊗C, so that B becomes identified as a complete subalgebra of B ⊗C
and V (B) as a subclass of V (B⊗C). (Notice that this amounts to taking e, and
hence ¯e, as the identity map.)
Since
V (B) |= C is a P (B)(C)-complete Boolean algebra,
it follows from Corollary 1.21 that
V (B⊗C) |= C is a P (B)(C)-complete Boolean algebra.
We are going to show that, in V (B⊗C), C contains a P (B)(C)-complete ultrafilter.
Define the object U + ∈V (B⊗C) by dom(U +) = B ⊗C and U +(a) = a for all
a ∈B ⊗C. That is, U + is the identify map on B ⊗C. Then, for a ∈B ⊗C, we
have
[PDF-GLYPH-U+0001]a ∈U +[PDF-GLYPH-U+0002] = a.
(6.18)
To prove this, we note first that since the map e is now the identify, Lemma 6.16
becomes, for x, y ∈B ⊗C, b ∈B,
b ≤[PDF-GLYPH-U+0001]x ≤C y[PDF-GLYPH-U+0002] ↔b ∧x ≤B⊗C y.
(6.19)
Now [PDF-GLYPH-U+0001]x = a[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]x ≤C a[PDF-GLYPH-U+0002], so taking b = [PDF-GLYPH-U+0001]x = a[PDF-GLYPH-U+0002] we get from Lemma 6.16,
[PDF-GLYPH-U+0001]x = a[PDF-GLYPH-U+0002] ∧x ≤B⊗C a.

```

## PDF page 153 | printed page 133

```text
ITERATED BOOLEAN EXTENSIONS
133
Thus
[PDF-GLYPH-U+0001]a ∈U +[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0004]
x∈B⊗C
[PDF-GLYPH-U+0001]x = a[PDF-GLYPH-U+0002] ∧x ≤a
and the reverse inequality follows from Theorem 1.17 (ii).
Our next result is crucial.
Theorem 6.20
V (B⊗C) |= U + is a P (B)(C)-complete ultrafilter in C.
Proof The proof proceeds somewhat along the lines of Theorem 4.21 (of which
the present theorem is actually a generalization), only it is a little more trouble-
some. We shall only verify two of the properties that U + must have, leaving the
verification of the others to the reader.
(a) [PDF-GLYPH-U+0001]∀xy ∈U +[x ∧C y ∈U +][PDF-GLYPH-U+0002] = 1. To verify this, observe that the l.h.s. is:
[PDF-GLYPH-U+0006]
a,b∈B⊗C
[U +(a) ∧U +(b)] ⇒[PDF-GLYPH-U+0001]a ∧C b ∈U +[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0006]
a,b∈B⊗C
[a ∧b ⇒a ∧b] = 1.
(b) [PDF-GLYPH-U+0001]∀X ∈P (B)(C)[[PDF-GLYPH-U+0003]
C X ∈U + →U + ∩X ̸= ∅][PDF-GLYPH-U+0002] = 1. To verify this, notice
that the l.h.s. is
[PDF-GLYPH-U+0006]
X∈dom(P (B)(C))
[PDF-GLYPH-U+0003]
X ⊆C ∧
[PDF-GLYPH-U+0004]
C
X ∈U +[PDF-GLYPH-U+0004]
⇒[PDF-GLYPH-U+0001]U + ∩X ̸= ∅[PDF-GLYPH-U+0002].
Given X
∈dom(P (B)(C)), take Y
∈V (B) to satisfy the conditions of
Lemma 6.17. Then
[PDF-GLYPH-U+0003]
X ⊆C ∧
[PDF-GLYPH-U+0004]
C
X ∈U +[PDF-GLYPH-U+0004]
≤
[PDF-GLYPH-U+0003] [PDF-GLYPH-U+0004]
C
Y ∈U +[PDF-GLYPH-U+0004]
.
Now, by Lemma 6.11 there is an a ∈B ⊗C such that [PDF-GLYPH-U+0001]a = [PDF-GLYPH-U+0003]
C Y [PDF-GLYPH-U+0002] = 1 and also
such that a = [PDF-GLYPH-U+0003]
B⊗C dom(Y ). Therefore
[PDF-GLYPH-U+0003] [PDF-GLYPH-U+0004]
C
Y ∈U +[PDF-GLYPH-U+0004]
= [PDF-GLYPH-U+0001]a ∈U +[PDF-GLYPH-U+0002] = a =
[PDF-GLYPH-U+0004]
B⊗C
dom(Y ).

```

## PDF page 154 | printed page 134

```text
134
ITERATED BOOLEAN EXTENSIONS
Hence
[PDF-GLYPH-U+0003]
X ⊆C ∧
[PDF-GLYPH-U+0004]
C
X ∈U +[PDF-GLYPH-U+0004]
≤
[PDF-GLYPH-U+0004]
B⊗C
dom(Y )
=
[PDF-GLYPH-U+0004]
x∈dom(Y )
[x ∈U +[PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]∃x ∈Y [x ∈U +][PDF-GLYPH-U+0002]
= [PDF-GLYPH-U+0001]U + ∩Y ̸= ∅[PDF-GLYPH-U+0002].
So
[PDF-GLYPH-U+0003]
X ⊆C ∧
[PDF-GLYPH-U+0004]
C
X ∈U +[PDF-GLYPH-U+0004]
≤[PDF-GLYPH-U+0001]U + ∩Y ̸= ∅[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]X ⊆C[PDF-GLYPH-U+0002]
≤[PDF-GLYPH-U+0001]U + ∩Y ̸= ∅∧Y = X ∪{0C}[PDF-GLYPH-U+0002]
≤[PDF-GLYPH-U+0001]U + ∩X ̸= ∅[PDF-GLYPH-U+0002],
and (b) follows.
Remarks
(1) Taking B = 2 and C =
ˆA in Theorem 6.20, where A is a
complete Boolean algebra in V , then 2 ⊗ˆA ∼= A and it is not hard to see that
U + is (essentially) the canonical generic ultrafilter in V (A). So Theorem 6.20
generalizes Theorem 4.21.
(2) Since V (B) ⊆V (B⊗C), we may regard V (B) as a class in V (B⊗C).
Moreover, it is not hard to see that, within V (B⊗C), V (B) is a transitive model
of ZFC containing all the ordinals. So working inside V (B⊗C) we can form the
C-extension (V (B))(C) of V (B). Now Theorem 6.20 may be construed as assert-
ing that, within V (B⊗C), U + is a V (B)-generic ultrafilter in C. Accordingly
within V (B⊗C) we can form the transitive collapse V (B)[U +] of the quotient
(V (B))(C)/U + and by applying Theorem 4.22 within V (B⊗C) we have
V (B⊗C) |= V (B)[U +] is the model of ZFC generated by U + and V (B).
Now, writing U∗for the canonical generic ultrafilter in V (B⊗C), it is shown in
Problem 6.36 that
V (B⊗C) |= U∗∈V (B)[U +].
(6.21)
Moreover, we know from the remarks following Lemma 4.25 that
V (B⊗C) |= ∀x[x ∈ˆV [U∗]]
(6.22)

```

## PDF page 155 | printed page 135

```text
ITERATED BOOLEAN EXTENSIONS
135
and so we get, using (6.21)
V (B⊗C) |= ∀x[x ∈V (B)[U +]].
(6.23)
In other words, V (B⊗C) may be regarded as the Boolean-valued model of ZFC
generated by V (B) and U +.
Notice also that if U◦is the canonical generic ultrafilter in V (B) then V (B) |=
∀x[x ∈ˆV [U◦]] and so we get, using (6.22) and (6.23),
V (B⊗C) |= ∀x[x ∈ˆV [U◦][U +]]
V (B⊗C) |= ˆV [U∗] = ˆV [U◦][U +].
The first of these expressions tells us that V (B⊗C) may be regarded as a ‘double
generic extension’ of ˆV , and the second that this double extension is expressible
as a single extension.
(3) Working within V (B⊗C), let iU + = i be canonical map of (V (B))(C) onto
V (B)[U+]. It follows from (6.23) that within V (B⊗C) this map carries (V (B))(C)
onto the universe, that is,
V (B⊗C) |= ∀x[x ∈i[(V (B))(C)]].
(6.24)
Now let J(C) be the class
J(C) = {x ∈V (B) : [PDF-GLYPH-U+0001]x ∈V (C)[PDF-GLYPH-U+0002]B = 1};
that is, J(C) is the class of all B-valued sets which, with probability 1, are
members of (V (B))(C). J(C) may be deemed to be the class that represents
(V (B))(C) in the real world. We may regard J(C) as a (B ⊗C)-valued structure
by defining, for x, y ∈J(C),
[PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002]J(C) = unique a ∈B ⊗C such that V (B) |= a = [PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002]C
[PDF-GLYPH-U+0001]x ∈y[PDF-GLYPH-U+0002]J(C) = unique a ∈B ⊗C such that V (B) |= a = [PDF-GLYPH-U+0001]x ∈y[PDF-GLYPH-U+0002]C.
Next, let us agree to identify elements of J(C) (and V (B⊗C)) when they are equal
with probability 1. Having done this, we can define the map j : J(C) →V (B⊗C)
by putting, for each x ∈J(C),
j(x) = unique y ∈V (B⊗C)such that V (B⊗C) |= y = i(x).
Using (6.23) and (6.18) it is now easy to verify that j is an isomorphism of
the Boolean-valued structures J(C) and V B⊗C. That is, j is a map of J(C)

```

## PDF page 156 | printed page 136

```text
136
ITERATED BOOLEAN EXTENSIONS
onto V (B⊗C) such that [PDF-GLYPH-U+0001]x = y[PDF-GLYPH-U+0002]J(C) = [PDF-GLYPH-U+0001]j(x) = j(y)[PDF-GLYPH-U+0002]B⊗C and [PDF-GLYPH-U+0001]x ∈y[PDF-GLYPH-U+0002]J(C) =
[PDF-GLYPH-U+0001]j(x) ∈j(y)[PDF-GLYPH-U+0002]B⊗C for all x, y ∈J(C). Accordingly, we have shown that the ‘iter-
ated’ Boolean extension V (B)(C) is equivalent to the ‘ordinary’ Boolean extension
V (B⊗C).
Our final result in this section is the following.
Lemma 6.25 If B satisfies ccc and V (B) |= C satisfies ccc, then B ⊗C
satisfies ccc.
Proof Let A = {aξ : ξ < ω1} be an antichain in B ⊗C; we show that there is
ξ0 < ω1 such that aη = 0 for all η > ξ0. Let A′ = A × {1}; then clearly
(1) V (B) |= A′ is an antichain in C.
Since C satisfies ccc in V (B), it follows from (1) that
(2) V (B) |= A′ is countable.
Now define f ∈V (B) by
f = {⟨ˆξ, aξ⟩(B) : ξ < ω1} × {1}.
It is then easily verified that
(3) V (B) |= f : ˆω1 →A′
and, for all ξ < ω1
(4) [PDF-GLYPH-U+0001]f(ˆξ) = aξ[PDF-GLYPH-U+0002] = 1.
Since B satisfies ccc, we have, by Theorem 1.51,
V (B) |= ˆω1 is uncountable
and it follows from (2) and (3) that
V (B) |= ∃ξ < ω1∀η > ξ∀η′ > ξ[f(η) = f(η′)].
Therefore, by the Maximum Principle, there is ξ ∈V (B) such that
(5) V B |= ξ < ˆω1 ∧∀η > ξ∀η′ > ξ[f(η) = f(n′)].
Since B satisfies ccc, by Theorem 1.51(v) there is an ordinal ξ0 < ω1 such that
[PDF-GLYPH-U+0001]ξ < ˆξ0[PDF-GLYPH-U+0002] = 1. It follows from (5) that
V (B) |= ∀η > ˆξ0[f(η) = f(ˆξ0)].

```

## PDF page 157 | printed page 137

```text
FURTHER RESULTS ON BOOLEAN ALGEBRAS
137
Hence [PDF-GLYPH-U+0001]f(ˆη) = f(ˆξ0)[PDF-GLYPH-U+0002] = 1 whenever ξ0 < η < ω1. Thus, by (4), [PDF-GLYPH-U+0001]aξ = aη[PDF-GLYPH-U+0002] = 1
whenever ξ0 < η < ω1. But since A is an antichain we have, for η > ξ0,
1 = [PDF-GLYPH-U+0001]aξ0 = aη[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]aη = aξ0 ∧aη[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]aη = 0[PDF-GLYPH-U+0002].
Therefore aη = 0 in B ⊗C for η > ξ0, as claimed.
Further results on Boolean algebras
In this section we give some technical results on Boolean algebras that we shall
require for the proof of relative consistency of SH.
Our first result is a generalization of Lemma 2.10.
Lemma 6.26 Let B be a complete Boolean algebra satisfying ccc, and let D be
a dense subset of B. Then for each b ∈B there is a countable subset Db of D
such that b = [PDF-GLYPH-U+0003] Db. Moreover, |B| ≤|D|ℵ0.
Proof Using Zorn’s lemma, let Db be a maximal antichain in the set {x ∈D :
x ≤b}. Put a = [PDF-GLYPH-U+0003] Db; we claim that a = b. Clearly a ≤b. On the other hand,
consider b −a. If it is nonzero, then there is d ∈D such that 0 ̸= d ≤b −a. But
then d is disjoint from every member of Db, contradicting the latter’s maximality.
It follows that b −a = 0, so a = b.
Thus b = [PDF-GLYPH-U+0003] Db; and since B satisfies ccc, Db, as an antichain, must be
countable.
Consequently each member of B is determined by a countable subset of D;
since there are at most |D|ℵ0 of these, the claimed inequality follows.
Corollary 6.27 Suppose κ is a regular uncountable cardinal, B is a complete
Boolean algebra satisfying ccc such that |B| ≤κ and C ∈V (B) satisfies
V (B) |=C is a complete Boolean algebra, satisfies
ccc and has a dense subset of cardinality < ˆκ.
Then for some cardinal λ < κ, |B ⊗C| ≤κλ.
Proof Let Q ∈V (B) be such that
[PDF-GLYPH-U+0001]Q is dense in C and |Q| < ˆκ[PDF-GLYPH-U+0002] = 1
and let Q′ = {x ∈B ⊗C : [PDF-GLYPH-U+0001]x ∈Q[PDF-GLYPH-U+0002] = 1}. Then, using Theorem 1.51(v), there
is an ordinal α < κ such that [PDF-GLYPH-U+0001]|Q| < ˆα[PDF-GLYPH-U+0002] = 1. Putting λ = |α| < κ (or λ = ω
if α is finite), we claim first that |Q′| ≤κλ. To see this, observe that since
[PDF-GLYPH-U+0001]|Q| < ˆα[PDF-GLYPH-U+0002] = 1 the Maximum Principle yields an f ∈V (B) such that [PDF-GLYPH-U+0001]f is a map

```

## PDF page 158 | printed page 138

```text
138
ITERATED BOOLEAN EXTENSIONS
of ˆα onto Q[PDF-GLYPH-U+0002] = 1. Each x ∈Q′ is then uniquely determined by the function
gx : α →B defined by gx(γ) = [PDF-GLYPH-U+0001]f(ˆγ) = x[PDF-GLYPH-U+0002]. Since there are at most κλ such
functions gx, the claim follows.
We next claim that the set
S = {b ∧x : 0 ̸= b ∈B ∧x ∈Q′}
is dense in B ⊗C. For suppose 0 ̸= c ∈B ⊗C. Then [PDF-GLYPH-U+0001]c ∈C[PDF-GLYPH-U+0002] = 1 and [PDF-GLYPH-U+0001]c ̸= 0C[PDF-GLYPH-U+0002] =
b ̸= 0. Put d = b · c + b∗· 1. Then [PDF-GLYPH-U+0001]d = c[PDF-GLYPH-U+0002] ≥b, [PDF-GLYPH-U+0001]d ∈C[PDF-GLYPH-U+0002] = 1 and [PDF-GLYPH-U+0001]d ̸= 0C[PDF-GLYPH-U+0002] = 1.
Since [PDF-GLYPH-U+0001]Q is dense in C[PDF-GLYPH-U+0002] = 1, there is x ∈Q′ such that [PDF-GLYPH-U+0001]x ≤C d[PDF-GLYPH-U+0002] = 1. It follows
that
b ≤[PDF-GLYPH-U+0001]c = d[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]c = d[PDF-GLYPH-U+0002] ∧[PDF-GLYPH-U+0001]x ≤C d[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]x ≤C c[PDF-GLYPH-U+0002].
So, by (6.19), b ∧x ≤c, and the claim follows.
Now we have |S| ≤|Q′| · |B| ≤κλ · κ = κλ. Therefore, by Lemma 6.26,
|B ⊗C| ≤|S|ℵ0 ≤κλ·ℵ0 = κλ.
We recall (see the remark after Lemma 2.3) that for each Boolean algebra A
there is a complete Boolean algebra B called the completion of A such that (if we
identify A as a subalgebra of B via the canonical monomorphism f : A →B)
(i) A is a subalgebra of B;
(ii) A −{0} is dense in B;
(iii) if X ⊆A has a join [PDF-GLYPH-U+0003]
A X in A, then [PDF-GLYPH-U+0003]
A X = [PDF-GLYPH-U+0003]
B X.
Let ⟨Bi : i ∈1⟩be a chain of (complete) Boolean algebras; that is, such
that for any pair Bi, Bj, one is a subalgebra of the other. Then we can form the
direct limit lim
−→Bi of the chain in the category of Boolean algebras in the usual
way: lim
−→Bi is just [PDF-GLYPH-U+0015]
i∈I Bi with Boolean operations inherited from the Bi in the
obvious manner. The completion of lim
−→Bi is called the limit completion of the
chain ⟨Bi : i ∈I⟩and is written limcoi∈IBi or limcoBi. Clearly limcoBi includes
[PDF-GLYPH-U+0015]
i∈I Bi −{0} as a dense subset.
Now let α be a limit ordinal. A sequence ⟨Bξ : ξ < α⟩of complete Boolean
algebras is called a normal sequence if
(a) B0 = 2;
(b) for ξ < η, Bξ is a complete subalgebra of Bη;
(c) for limit β, Bβ = limcoξ<βBξ.

```

## PDF page 159 | printed page 139

```text
FURTHER RESULTS ON BOOLEAN ALGEBRAS
139
Lemma 6.28 Let ⟨Bξ : ξ < α⟩be a normal sequence of complete Boolean
algebras and let B = limcoξ<αBξ. Then each Bξ is a complete subalgebra of B.
Suppose, further, that each Bξ satisfies ccc and that α is an uncountable regular
cardinal. Then
(i) B =
[PDF-GLYPH-U+0005]
ξ<α Bξ;
(ii) if |X| < α and f : X →B, then ran(f) ⊆Bξ for some ξ < α.
Proof Let X ⊆Bξ and a = [PDF-GLYPH-U+0003] X in Bξ. We claim that α = [PDF-GLYPH-U+0003] X in lim
−→Bη = B′.
For if not, then X would have an upper bound b < a in B′. Since B′ = [PDF-GLYPH-U+0015] Bη
there is η < α such that b ∈Bη, and without loss of generality we may suppose
that ξ ≤η. But then, in Bη, [PDF-GLYPH-U+0003] X ≤b < a, contradicting the assumption that Bξ
is a complete subalgebra of Bη. Therefore [PDF-GLYPH-U+0003]
B X = [PDF-GLYPH-U+0003]
B′ X and, since B is the
completion of B′, [PDF-GLYPH-U+0003]
B′ X = [PDF-GLYPH-U+0003]
B X. So Bξ is complete subalgebra of B.
We next prove (i). Let x ∈B. Since [PDF-GLYPH-U+0015]
ξ<α Bξ −{0} is dense in B, by
Lemma 6.26 there is a countable set {xn : n ∈ω} such that xn ∈Bξn with
ξn < α and x = [PDF-GLYPH-U+0003]
n∈ω xn. Since λ is regular, there is ξ < α such that ξ ≥ξn for
all n, so that xn, ∈Bξ for all n, whence x = [PDF-GLYPH-U+0003]
n∈ω xn ∈Bξ. (i) follows.
Finally, (ii) follows easily from (i) and the regularity of α.
Corollary 6.29 Let κ be an uncountable regular cardinal, ⟨Bξ : ξ < k⟩be a
normal sequence of complete Boolean algebras satisfying ccc and let B = limcoBξ.
Suppose further that X ∈V (B) satisfies (a) [PDF-GLYPH-U+0001]|X| < κ[PDF-GLYPH-U+0002] = 1 and (b) either [PDF-GLYPH-U+0001]X ⊆
ˆκ[PDF-GLYPH-U+0002] = 1 or [PDF-GLYPH-U+0001]X ⊆ˆκ× ˆκ[PDF-GLYPH-U+0002] = 1 or [PDF-GLYPH-U+0001]X ⊆P ˆκ∧| [PDF-GLYPH-U+0015] X| < ˆκ][PDF-GLYPH-U+0002] = 1. Then there are ξ < κ
and Y ∈V (Bξ) such that [PDF-GLYPH-U+0001]Y = X[PDF-GLYPH-U+0002] = 1.
Proof Since κ and κ × κ are naturally bijective and each X ⊆Pκ such that
|X| < κ is naturally correlated with a subset of κ × κ, the proof reduces to the
case in which [PDF-GLYPH-U+0001]X ⊆ˆκ[PDF-GLYPH-U+0002] = 1. By Theorem 1.51(iv) we know that [PDF-GLYPH-U+0001]ˆκ is regular[PDF-GLYPH-U+0002] = 1
and since [PDF-GLYPH-U+0001]|X| < ˆκ[PDF-GLYPH-U+0002] = 1 it follows (using the Maximum Principle) that there is
α ∈V (B) such that
[PDF-GLYPH-U+0001]α < ˆκ ∧∀ξ ≥α[ξ /∈X][PDF-GLYPH-U+0002] = 1.
By Theorem 1.51(v) there is an ordinal γ < κ such that [PDF-GLYPH-U+0001]α < ˆγ[PDF-GLYPH-U+0002] = 1. It follows
that
(1)
[PDF-GLYPH-U+0001]ˆξ ∈X[PDF-GLYPH-U+0002] = 0 for all ξ ≥γ.
Now define Y ∈V (B) by dom(Y ) = {ˆξ : ξ < γ} and Y (ˆξ) = [PDF-GLYPH-U+0001]ˆξ ∈X[PDF-GLYPH-U+0002]. It is
then easily verified, using (1), that [PDF-GLYPH-U+0001]X = Y [PDF-GLYPH-U+0002] = 1. So it remains to show that

```

## PDF page 160 | printed page 140

```text
140
ITERATED BOOLEAN EXTENSIONS
Y ∈V (Bξ) for some ξ < κ. But this follows immediately from an application of
Lemma 6.28 to the map f : γ →B given by f(ξ) = Y (ˆξ).
Now let B be a complete Boolean algebra and let C be a complete subalgebra
of B. We define the map π : B →C as follows.
π(x) =
[PDF-GLYPH-U+0006]
{y ∈C : x ≤y}.
Notice that we then have, for b ∈B, c ∈C, the ‘adjointness’ condition:
b ≤c ↔π(b) ≤c,
(6.30)
which in turn characterizes π uniquely. The π is called the canonical projection
of B onto C.
Lemma 6.31 The canonical projection π
:
B
→
C has the following
properties:
(i) π(x) ≥x;
(ii) x ≤y →π(x) ≤π(y);
(iii) π(c) = c for all c ∈C;
(iv) π([PDF-GLYPH-U+0003] X) = [PDF-GLYPH-U+0003] π[X] for all X ⊆B;
(v) π(b) ∧c = π(b ∧c) for all b ∈B, c ∈C.
Proof (i), (ii), and (iii) are obvious. To prove (iv), we note that, if c ∈C then
π(
[PDF-GLYPH-U+0004]
X) ≤c ↔
[PDF-GLYPH-U+0004]
X ≤c
(by (6.30))
↔∀x ∈X[x ≤c]
↔∀x ∈X[π(x) ≤c]
(by (6.30))
↔
[PDF-GLYPH-U+0004]
π[X] ≤c.
As for (v), we have π(b) ∧c = π(b) ∧π(c) ≥π(b ∧c) by (ii) and (iii). On the
other hand,
π(b) = π(b ∧c) ∨π(b ∧c∗)
(by (iv))
≤π(b ∧c) ∨c∗
(by (ii) and (iii)).
So π(b) ∧c ≤π(b ∧c) ∧c ≤π(b ∧c) and the result follows.
Our final preparatory result concerns the preservation of the countable chain
condition under passage to limit completions.

```

## PDF page 161 | printed page 141

```text
FURTHER RESULTS ON BOOLEAN ALGEBRAS
141
Theorem 6.32 Let ⟨Bξ : ξ < α⟩be a normal sequence of complete Boolean
algebras, and suppose that each Bξ satisfies ccc. Then the limit completion B of
⟨Bξ : ξ < α⟩also satisfies ccc.
Proof We first reduce the proof of the theorem to the case in which α = ω1.
Suppose the hypothesis of the theorem true and the conclusion false. Let A be
an antichain in B of cardinality ℵ1 such that 0 /∈A. Since [PDF-GLYPH-U+0015]
ξ<α Bξ is dense in
B, for each a ∈A we can find an ordinal γa < α and an element ba ∈Bγa such
that 0 ̸= ba ≤a. Clearly {ba : a ∈A} is an antichain in B of cardinality ℵ1.
Also, sup {γa : a ∈A} = α, for otherwise there would be an ordinal β < α
for which γa < β for a ∈A, contradicting the assumption that Bβ satisfies ccc.
Since |A| = ℵ1, it follows that α is cofinal with ω1.
On the other hand, α is not cofinal with ω. For if α = sup{αn : n ∈ω} then
for each a ∈A there is n ∈ω such that γa < αn. Hence {ba : a ∈A} ⊆[PDF-GLYPH-U+0015]
n∈ω Bαn
and so, for some n, Bαn ∩{ba : a ∈A} must have cardinality ℵ1. This contradicts
the assumption that Bαn satisfies ccc.
It follows that α has cofinality ω1. Accordingly there is a sequence of ordinals
⟨βξ : ξ < ω1⟩such that
β0 = 0, η < ξ →βη < βξ, α = sup{βξ : ξ < ω1}
and βξ = sup{βη : η < ξ} for limit ξ.
If we put B′
ξ for Bβξ, then ⟨B′
ξ : ξ < ω1⟩is a normal sequence, each Bξ satisfies
ccc, but the limit completion Bα of ⟨B′
ξ : ξ < ω1⟩does not.
Thus we need only prove the theorem when α = ω1. Let X be an antichain
in B; we show that X is countable.
Without loss of generality we may assume that [PDF-GLYPH-U+0003] X
= 1 and, since
[PDF-GLYPH-U+0015]
ξ<ω1 Bξ −{0} is dense in B, that X ⊆[PDF-GLYPH-U+0015]
ξ<ω1 Bξ. For ξ < ω1, put Xξ = X ∩Bξ.
Since Bξ satisfies ccc, Xξ is countable.
Now by Lemma 6.28, Bξ is a complete subalgebra of B and so we can consider
the canonical projection πξ of B onto Bξ. By Lemma 6.31 (iv), we have
1 = πξ
[PDF-GLYPH-U+001F][PDF-GLYPH-U+0004]
X

=
[PDF-GLYPH-U+0004]
πξ[X].
Since Bξ satisfies ccc, there is, by Problem 1.53 (iv), a countable subset X′ of X
such that
1 =
[PDF-GLYPH-U+0004]
πξ[X′].
It follows that for some countable ordinal δξ we have X′ ⊆Xδξ and
1 =
[PDF-GLYPH-U+0004]
πξ[Xδξ].
(1)

```

## PDF page 162 | printed page 142

```text
142
ITERATED BOOLEAN EXTENSIONS
Now let γ be a countable limit ordinal such that δξ < γ for all ξ < γ. We claim
that X = Xγ. Since Xγ is countable, this will complete the proof.
For ξ < γ we have
[PDF-GLYPH-U+0004]
πξ[Xδξ] = πξ
[PDF-GLYPH-U+001F][PDF-GLYPH-U+0004]
Xδξ

≤πξ
[PDF-GLYPH-U+001F][PDF-GLYPH-U+0004]
Xγ

,
so it follows from (1) that
1 = πξ
[PDF-GLYPH-U+001F][PDF-GLYPH-U+0004]
Xγ

.
(2)
We claim that [PDF-GLYPH-U+0003] Xγ = 1. For if not, then since [PDF-GLYPH-U+0015]
ξ<γ Bξ −{0} is dense in Bγ,
there is ξ < γ and 0 ̸= b ∈Bξ such that b ∧[PDF-GLYPH-U+0003] Xγ = 0. Hence, by Lemma 6.31(v)
0 = πξ
[PDF-GLYPH-U+001F]
b ∧
[PDF-GLYPH-U+0004]
Xγ

= b ∧πξ
[PDF-GLYPH-U+001F][PDF-GLYPH-U+0004]
Xγ

.
But this contradicts (2).
Therefore [PDF-GLYPH-U+0003] Xγ = 1 and it follows easily from this that X = Xγ.
Notice that Theorem 6.32 yields as an immediate corollary the result that
the direct limit of a normal sequence of complete Boolean algebras satisfying ccc
also satisfies ccc.
The relative consistency of SH
At long last we are in a position to prove the relative consistency of
MA + 2ℵ0 > ℵ1, and so of SH.
Theorem 6.33 Let κ be an uncountable regular cardinal such that for any
0 ̸= λ < κ we have κλ = κ. Then there is a complete Boolean algebra B such that
V (B) |= MA + 2ℵ0 = ˆκ.
Proof We construct recursively a normal sequence ⟨Bξ : ξ < κ⟩of complete
Boolean algebras such that, for all ξ < κ, (a) Bξ satisfies ccc and (b) |Bξ| ≤κ.
For each complete Boolean algebra B satisfying ccc such that |B| ≤κ,
let D(B) be a core for the V (B)-set {x : x ⊆ˆκ × ˆκ ∧|x| < ˆκ}(B). We claim
that |D(B)| ≤κ. To prove this we note first that if x ∈D(B) then, since [PDF-GLYPH-U+0001]ˆκ is
regular [PDF-GLYPH-U+0002] = 1 by Theorem 1.51(iv) there is α ∈V (B) such that [PDF-GLYPH-U+0001]α < ˆκ ∧x ⊆
α×α[PDF-GLYPH-U+0002] = 1 and hence by Theorem 1.51(v) an ordinal β < κ such that [PDF-GLYPH-U+0001]α < ˆβ[PDF-GLYPH-U+0002] = 1.
Therefore [PDF-GLYPH-U+0001]x ⊆ˆβ × ˆβ[PDF-GLYPH-U+0002] = 1. It follows that if for each β < κ we let vβ be a core
for the V (B)-set P (B)(ˆβ × ˆβ) then |D(B)| ≤| [PDF-GLYPH-U+0015]
β<κ vβ| ≤Σβ<κ|vβ|. Now if for
each z ∈vβ we define fz : β × β →B by fz(ξ, η) = [PDF-GLYPH-U+0001]⟨ˆξ, ˆη⟩∈z[PDF-GLYPH-U+0002], then it is easily

```

## PDF page 163 | printed page 143

```text
THE RELATIVE CONSISTENCY OF SH
143
verified that the map z [PDF-GLYPH-U+0017]→fz is a bijection between vβ and Bβ×β. It follows that
|vβ| ≤κ|β| = κ. Therefore |D(B)| ≤Σβ<κ|vβ| ≤κ · κ = κ as claimed.
For each complete Boolean algebra B satisfying ccc such that |B| ≤κ, we fix
an enumeration ⟨RB
ξ : ξ < κ⟩of D(B).
Now we put B0 = 2, and for α satisfying 0 < α < κ assume as inductive
hypothesis that ⟨Bξ : ξ < α⟩has been constructed so as to be a normal sequence
satisfying (a) and (b).
If α is a limit ordinal, we put Bα = limcoξ<αBξ. If α is a successor ordinal, say
ξ +1, we construct Bα = Bξ+1 as follows. Let ξ [PDF-GLYPH-U+0017]→⟨βξ, γξ⟩be the canonical map
of κ onto κ × κ (see Chapter 0). Recall that βξ ≤ξ for any ξ < κ. Let A = Bβξ;
then by inductive hypothesis A is a complete subalgebra of Bξ and |A| ≤κ.
Putting R = RA
γξ, we have R ∈V (Bξ). In V (Bξ), let ∆(R) = ⟨{x : ⟨x, x⟩∈R}, R⟩,
and put
b = [PDF-GLYPH-U+0001]∆(R) is a Boolean algebra satisfying ccc[PDF-GLYPH-U+0002].
Let C′
ξ be the two-term mixture:
C′
ξ = b · ∆(R) + b∗· ˆ2;
then
[PDF-GLYPH-U+0001]C′
ξ is a Boolean algebra satisfying ccc[PDF-GLYPH-U+0002] = 1.
Let Cξ ∈V (B) satisfy
V (Bξ) |= Cξ is the completion of C′
ξ.
Note that
V (Bξ) |= Cξ satisfies ccc.
We finally put
Bξ+1 = Bξ ⊗Cξ,
and identify Bξ with its canonical image in Bξ ⊗Cξ, so that Bξ becomes a
complete subalgebra of Bξ+1.
Clearly ⟨Bξ : ξ < κ⟩constructed in this way is a normal sequence. We now
verify (a) and (b).
(a) is proved by induction on ξ. B0 = 2 clearly satisfies ccc. If Bξ satisfies
ccc, then Bξ+1 = Bξ ⊗Cξ satisfies ccc by Lemma 6.25. If α is a limit ordinal
and Bξ satisfies ccc for all ξ < α, then Bα, as the limit completion of the normal
sequence ⟨Bξ : ξ < α⟩, satisfies ccc by Theorem 6.32. So (a) follows.

```

## PDF page 164 | printed page 144

```text
144
ITERATED BOOLEAN EXTENSIONS
(b) is also proved by induction on ξ. Clearly |B0| ≤κ. If α is a limit ordinal
then Bα has the dense subset [PDF-GLYPH-U+0015]
ξ<α Bξ −{0} of cardinality ≤κ by inductive
hypothesis, so, since Bα satisfies ccc, |Bα| ≤κℵ0 = κ by Lemma 6.26. If ξ < κ
and |Bξ| ≤κ, we observe that
V (Bξ) |= Cξ satisfies ccc and has a dense subset C′
ξ such that |C′
ξ| < ˆκ,
so |Bξ+1| = |Bξ ⊗Cξ| ≤κ by Corollary 6.27.
Now we define B to be the limit completion of ⟨Bξ : ξ < κ⟩. Then by
Theorem 6.32 B satisfies ccc and since it has the dense subset [PDF-GLYPH-U+0015]
ξ<κ Bξ −{0} of
cardinality ≤κ, it follows from Lemma 6.26 that |B| ≤κℵ0 = κ. Therefore by
Problem 2.19(i), we have
V (B) |= 2ℵ0 ≤(κℵ0)[PDF-GLYPH-U+0001]= ˆκ.
Thus, if we can show that MAˆκ holds in V (B), we will have, by Lemma 6.6,
V (B) |= ˆκ ≤2ℵ0, whence V (B) |= ˆκ = 2ℵ0 and so, in V (B), MAˆκ is just MA. It
will therefore follow that
V (B) |= 2ℵ0 = ˆκ ∧MA.
So it remains to show that
V (B) |= MAˆκ.
By Theorem 6.8 and Corollary 1.28(ii) it suffices to show that, if A, R, S ∈V (B)
satisfy
(1) V (B) |= ⟨A, R⟩is Boolean algebra satisfying ccc ∧|A| < ˆκ ∧S ⊆PA ∧
|S| < ˆκ,
then
V (B) |= there is an S-complete ultrafilter in ⟨A, R⟩.
Without loss of generality we may assume that V (B) |= A ⊆ˆκ and so
(2) V (B) |= R ⊆ˆκ × ˆκ ∧|R| < ˆκ ∧S ⊆P ˆκ ∧|S ∪[PDF-GLYPH-U+0015] S| < ˆκ.
By Corollary 6.29, there exist ξ < κ and A′, R′, S′ ∈V (Bξ) such that
[PDF-GLYPH-U+0001]A = A′[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]R = R′[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]S = S′[PDF-GLYPH-U+0002] = 1
and
so
we
may
assume
that
A, R, S ∈V (Bξ).
Now we claim that
(3) V (Bξ) |= ⟨A, R⟩is a Boolean algebra satisfying ccc ∧|A| < ˆκ ∧S ⊆PA ∧
|S| < ˆκ.

```

## PDF page 165 | printed page 145

```text
THE RELATIVE CONSISTENCY OF SH
145
Suppose, for example, [PDF-GLYPH-U+0001]|A| < ˆκ[PDF-GLYPH-U+0002]Bξ ̸= 1. Then [PDF-GLYPH-U+0001]|A| ≥ˆκ[PDF-GLYPH-U+0002]Bξ ̸= 0, so, for some
f ∈V (Bξ), [PDF-GLYPH-U+0001]f : ˆκ
one–one
−→A[PDF-GLYPH-U+0002]Bξ ̸= 0. By Corollary 1.21, and the fact that Bξ is a
complete subalgebra of B, [PDF-GLYPH-U+0001]f : ˆκ
one–one
−→A[PDF-GLYPH-U+0002]B ̸= 0. Therefore [PDF-GLYPH-U+0001]|ˆκ| ≤|A|[PDF-GLYPH-U+0002]B ̸= 0.
But since B satisfies ccc, we have [PDF-GLYPH-U+0001]ˆκ = |ˆκ|[PDF-GLYPH-U+0002]B = 1, so [PDF-GLYPH-U+0001]ˆκ ≤|A|[PDF-GLYPH-U+0002] ̸= 0. This
contradicts (1).
Similarly, if
[PDF-GLYPH-U+0001]⟨A, R⟩does not satisfy ccc[PDF-GLYPH-U+0002]Bξ ̸= 0,
then there is X ∈V (Bξ) such that
[PDF-GLYPH-U+0001]X is an antichain in A ∧|X| ≥ℵ1 = ˆℵ1[PDF-GLYPH-U+0002]Bξ ̸= 0.
So by Corollary 1.21
[PDF-GLYPH-U+0001]X is an antichain in A ∧|X| ≥ℵ1[PDF-GLYPH-U+0002]B ̸= 0,
whence
[PDF-GLYPH-U+0001]X is an uncountable antichain in A[PDF-GLYPH-U+0002]B ̸= 0.
But this contradicts (1). So (3) is proved.
It follows from (2) and the definition of D(Bξ) that there is R′′ ∈D(Bξ)
such that [PDF-GLYPH-U+0001]R = R′′[PDF-GLYPH-U+0002]Bξ = 1 and so without loss of generality we may assume that
R ∈D(Bξ). Choose η < κ to satisfy R = RBξ
η , and α < κ so that
βα = ξ, γa = η, α ≥βα = ξ.
Then A, R, and S are all in V (Bα) and reasoning similar to that used to prove
(3) shows that
V (Bα) |= ⟨A, R⟩is a Boolean algebra satisfying ccc.
We claim that an S-complete ultrafilter in ⟨A, R⟩was added in the passage
from V (Bα) to V (Bα+1).
Now Bα+1 = Bα ⊗Cα, so by Theorem 6.20 the object U + ∈V (Bα+1) satisfies
V (Bα+1) |= U + is a P (Bα)(Cα)-complete ultrafilter in Cα.
But, by construction we have
V (Bα) |= Cα is the completion of ⟨A, R⟩

```

## PDF page 166 | printed page 146

```text
146
ITERATED BOOLEAN EXTENSIONS
and since V (Bα+1) |= S ⊆P (Bα)(Cα) it follows that
V (Bα+1) |= U + ∩A is an S-complete ultrafilter in ⟨A, R⟩,
as required.
Since Bα+1 is a complete subalgebra of B, we get
V (Bα) |= U + ∩A is an S-complete ultrafilter in ⟨A, R⟩,
and the proof is complete.
Corollary 6.34 If ZF is consistent, so is ZFC + SH(+¬CH).
Proof Assuming GCH, take κ = ℵ2 in Theorem 6.33. We get B such that V (B) |=
MA + 2ℵ0 = ℵ2, whence, by Theorem 6.9, V (B) |= SH. The result now follows
from Theorem 1.19.
We conclude this chapter with some remarks on further results about SH that
have been obtained. Jensen has shown that V = L →¬ SH, which of course
yields another proof of the independence of SH. For an account of this proof,
see Devlin (1977). Jensen has also shown that SH + GCH is relatively consistent
with ZFC, but the proof is very involved: see Devlin and Johnsbraten (1974).
For more applications of Martin’s axiom, see Rudin (1977).
Problems
6.35 (The iteration theorem) Let M be a transitive ∈-model of ZFC, let B
be a complete Boolean algebra in the sense of M, let C, ≤C be elements of M (B)
such that M (B) |= ⟨C, ≤C⟩is a complete Boolean algebra, and let D = B ⊗C.
We identify B as a complete subalgebra of D.
(i) Let F be an M-generic ultrafilter in B and the let iF be the canonical map
of M (B) onto M[F]. Then iF (c) is a complete Boolean algebra (with partial
ordering iF (≤C)) in M[F]. Show that iF |D is an M-complete homomorph-
ism of D onto iF (C), that is, preserves the join of any subset of D, which is
at the same time a member of M. (Clearly iF [D] ⊆iF (C). To prove equal-
ity, use Lemma 1.32. To show that iF is M-complete, use the M-genericity
of F in the form: A ⊆F, A ∈M →[PDF-GLYPH-U+0002] A ∈F.)
(ii) A double generic extension is equivalent to a single one. Let F be an
M-generic ultrafilter in B, and let G be an M[F]-generic ultrafilter in
iF (C). Put H = i−1
F [G] ∩D. Show that H is an M-generic ultrafilter in D
and that M[H] = M[F][G]. (Use (i).)
(iii) Let H be an M-generic ultrafilter in D. Then F = B ∩H is an M-generic
ultrafilter in B. Put G = iF [H]; show that G is an M[F]-generic ultrafilter

```

## PDF page 167 | printed page 147

```text
THE RELATIVE CONSISTENCY OF SH
147
in iF (C) and that M[H] = M[F][G]. (Use Theorem 6.20 and the remarks
following it.)
6.36 (More on ⊗) Let B be an complete Boolean algebra and suppose that
V (B) |= ⟨C, ≤C⟩
is a Boolean algebra. Put A = B ⊗C and identify B as a
subalgebra of A (see Lemma 6.15). Then V (B) |= ˆA and ˆB are Boolean algebras
and ˆB is a subalgebra of
ˆA.
(i) Show that, for a ∈A, we have [PDF-GLYPH-U+0001]a = 1C[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0003]{b ∈B : b ≤a}. (Use (6.19.)
(ii) Define h ∈V (B) by h = {⟨ˆa, a⟩(B) : a ∈A} × {1}. Show that V (B) |= h is
a homomorphism of
ˆA onto C. (Note that [PDF-GLYPH-U+0001]h(ˆa) = a[PDF-GLYPH-U+0002] = 1 for a ∈A.)
(iii) Let U0 be the canonical generic ultrafilter in ˆB and, in V (B), let F = {x ∈
ˆA : ∃y ∈U0[y ≤x]}(B) be the filter in ˆA generated by U0. Show that
V (B) |= ∀x ∈A[h(x) = 1 ↔x ∈F] and deduce that V (B) |= C ∼= ˆA/F.
(Use (i).)
(iv) Let U + ∈V (A) be the ultrafilter in C defined before (6.18) (cf. The-
orem 6.20) and U∗∈V (A) be the canonical generic ultrafilter in ˆA. Show
that V (A) |= h−1[U +] = U∗and deduce that V (A) |= U∗∈V (B)[U +].
6.37 (The operation inverse to ⊗) Let A be a complete Boolean algebra and
let B be a complete subalgebra of A. Working inside V (B), let F be the filter
in ˆA generated by the canonical generic ultrafilter in ˆB (cf. Problem 6.35(iii)),
let A ∗B = ˆA/F and let π : ˆA →A ∗B be the natural epimorphism. Finally, let
p: A →V (B) be defined by [PDF-GLYPH-U+0001]p(a) = π(ˆa)[PDF-GLYPH-U+0002] = 1 for a ∈A.
(i) Show that, for x, y ∈A, b ∈B, b ∧x ≤b ∧y ↔b ≤[PDF-GLYPH-U+0001]p(x) ≤p(y)[PDF-GLYPH-U+0002] and
b ∧x = b ∧y ↔b ≤[PDF-GLYPH-U+0001]p(x) = p(y)[PDF-GLYPH-U+0002]. (Like Lemma 6.16.)
(ii) Let t ∈V (B) satisfy [PDF-GLYPH-U+0001]t ∈A ∗B[PDF-GLYPH-U+0002] = 1. Show that [PDF-GLYPH-U+0001]t = p(a)[PDF-GLYPH-U+0002] = 1 for some
a ∈A. (Take a to be a suitable mixture of members of A, and use (i).)
(iii) Show that [PDF-GLYPH-U+0001]A ∗B is complete[PDF-GLYPH-U+0002] = 1. (Given X ∈V (B) such that [PDF-GLYPH-U+0001]X ⊆
A ∗B ∧0 ∈X[PDF-GLYPH-U+0002] = 1, let a = [PDF-GLYPH-U+0003]{x ∈A : [PDF-GLYPH-U+0001]p(x) ∈X[PDF-GLYPH-U+0002] = 1}; use (i) and (ii)
to show that [PDF-GLYPH-U+0001]a = [PDF-GLYPH-U+0003] X[PDF-GLYPH-U+0002] = 1.)
(iv) Show that A ∼= B ⊗(A ∗B). (Show that p does the trick.)
(v) Show, inversely, that if
V (B) |= C is a complete Boolean algebra,
then C ∼= (B ⊗C) ∗B. (Use Problem 6.36(iii).)
6.38 (Injective Boolean algebras) A Boolean algebra B is said to be injective
if, for any Boolean algebra A, any homomorphism of a subalgebra of A into B can
be extended to the whole of A. B is said to be an absolute subretractif whenever

```

## PDF page 168 | printed page 148

```text
148
ITERATED BOOLEAN EXTENSIONS
B is a subalgebra of a Boolean algebra A there is an epimorphism from A to B
which is the identity on B.
(i) Let B be a complete Boolean algebra and let U∗be the canonical generic
ultrafilter in V (B). Show that the following conditions are equivalent:
(a) B is injective;
(b) B is an absolute subretract;
(c) for any Boolean algebra A of which B is a subalgebra, there is U ∈V (B)
such that V (B) |= U is an ultrafilter in (the Boolean algebra) ˆA and
U∗⊆U;
(d) for any C ∈V (B) such that V (B) |= C is a Boolean algebra, there is
U ∈V (B) such that V (B) |= U is an ultrafilter in C. (For (iii) →(iv),
use Problem 6.36(iii).)
(ii) Deduce the Sikorski Extension Theorem: any complete Boolean algebra is
injective.

```

## PDF page 169 | printed page 149

```text
7
BOOLEAN-VALUED ANALYSIS
In this chapter we give a brief introduction to real analysis in two types of
Boolean-valued model: those arising from measure algebras, and those arising
from algebras of projections on Hilbert space. For both of these models, facts
about real numbers holding in the model can be ‘externalized’ so as to yield
results about the mathematical objects to which these real numbers correspond
in V : in the first of these models, to measurable functions, and in the second,
to self-adjoint operators. We shall assume some familiarity with measure theory
and the theory of Hilbert spaces.
We begin with some general considerations on real numbers in Boolean-
valued models.
The ordered field of real numbers can be characterized as the unique complete
ordered field, up to isomorphism. In set theory there are a number of ways of
constructing such a field, for example, by Cauchy sequences or Dedekind cuts in
the ordered field Q of rationals. The results are, of course, all order-isomorphic
and the symbol R used to denote any one of them.
Now let B be a complete Boolean algebra and let R(B) ∈V (B) satisfy
V (B) |= R(B)is a complete ordered field.
Let RB be a core for R(B). We may assume that ˆr ∈RB for any r ∈R, and in
particular, writing 0 for the zero element of R, that ˆ0 is the zero of RB.
RB carries the structure of an ordered ring. The operations in this ring are
defined in the obvious way: for u, v ∈RB, u + v (resp. uv) is the unique w ∈RB
such that V (B) |= w = u + v (resp. V (B) |= w = uv). It is also an algebra over R
in which, for r ∈R, r · u is the unique w ∈RB such that V (B) |= w = ˆru. Order
in RB is defined by u ≤v iffV (B) |= u ≤v.
Note that, while RB is not a field, it is ‘almost’ a field in the sense that an
element x ∈RB is invertible iff[PDF-GLYPH-U+0001]x = ˆ0[PDF-GLYPH-U+0002] = 0B.
Boolean-valued models built from measure algebras
A σ-algebra is a Boolean algebra in which every countable subset has a join
and a meet. A σ-ideal in a σ-algebra is an ideal containing the joins of each of
its countable subsets. It is readily shown that the quotient of a σ-algebra by a
σ-ideal is itself a σ-algebra.

```

## PDF page 170 | printed page 150

```text
150
BOOLEAN-VALUED ANALYSIS
A σ-field of subsets of a set E is a field of subsets of E which is closed under
countable unions. By a measure space we mean a triple (E, S , µ) in which S is
a σ-field of subsets of a set E and µ is a σ-finite measure on S , that is, a function
on S taking values in R+ ∪{∞} such that (i) µ(∅) = 0; (ii) µ ([PDF-GLYPH-U+0015]∞
n=1 Xn) =
[PDF-GLYPH-U+0001]∞
n=1 µ(Xn) for any countable disjoint subfamily {Xn : n ∈ω} of S , (iii) there
exists a countable disjoint subfamily {Un: n ∈ω} of S such that for every n,
µ(Un) < ∞and [PDF-GLYPH-U+0015]∞
n=1 Un = E.
Let (E, S , µ) be a measure space. The family I = {X ∈S . µ(X) = 0} is
readily seen to be a σ-ideal in S , so that the quotient B = S /I is a σ-algebra.
The ideal I is the ideal of sets of µ-measure 0 and B the reduced measure
algebra of E. In B, the operations of meet, join and complement are represented
by their set-theoretic counterparts. Also equality of two elements b1 = S1/I ,
b2 = S2/I of B means that S1 and S2 differ only by a set of measure zero,
that is, they are almost equal. It can be shown (see, for example, Halmos 1965,
section 7, exercise 4) that B satisfies the ccc. Since a σ-algebra satisfying the
ccc is necessarily complete (see Halmos 1963, section 14, corollary to lemma 1),
B is complete.
We shall need to describe partitions of unity in B (see Ch. 1). If {Si: i ∈ω}
is a countable partition of unity in S , then, writing bi = Si/I , {bi: i ∈ω} is a
partition of unity in B. Using the fact that B satisfies the ccc, it is not hard to
show that every partition of unity in B arises in this way.
We now introduce the Boolean extension V (B). The natural numbers in V (B)
are then mixtures of the form [PDF-GLYPH-U+0001]
k∈ω bk · ˆnk where {nk: k ∈ω} is a set of natural
numbers and {bk: k ∈ω} is a partition of unity in B. Similarly, the rational
numbers in V (B) are of the form [PDF-GLYPH-U+0001]
k∈ω bk · ˆqk where {qk: k ∈ω} is a set of
rational numbers and {bk: k ∈ω} is a partition of unity in B. If bk = Sk/I as
above, then [PDF-GLYPH-U+0001]
k∈ω bk · ˆnk or [PDF-GLYPH-U+0001]
k∈ω bk · ˆqk may be identified with a step function
taking the value nk or qk on each Sk.
In order to identify the field R(B) of real numbers in V (B) we need to specify
a particular construction of R in V . For our present purposes we shall take R
to consist of the lower sections (minus their end points) of Dedekind cuts in Q.
Thus we shall define ‘r is a real number’ as
r ⊆Q ∧∃x ∈Q(x ∈r) ∧∃x ∈Q(x /∈r) ∧∀x ∈Q[x ∈r ↔∃y ∈Q(x < y ∧y ∈r)].
If we write the above formula as ϕ(r), then R(B) may be identified as the B-set
{r ∈PQ: ϕ(r)}(B), and RB as a core for this set.
With operations defined in the obvious way, the set of measurable real-vaued
functions on E also forms an algebra M(E). The subset I of functions that
are zero almost everywhere, that is, functions f for which {x: f(x) ̸= 0} has
measure 0, is an ideal in M(E). The following theorem now states the precise
sense in which the real numbers in V (B) may be identified with measurable
functions on E.

```

## PDF page 171 | printed page 151

```text
BOOLEAN-VALUED MODELS BUILT FROM MEASURE ALGEBRAS
151
Theorem 7.1 The algebra RB is isomorphic to the quotient algebra M(E)/I.
Sketch of proof Given u ∈RB, for each q ∈Q let
(∗)
bq = [PDF-GLYPH-U+0001]ˆq ∈u[PDF-GLYPH-U+0002].
Then from the above definition of real number it follows easily that the three
conditions below hold (with meets and joins calculated in B):
(1)
[PDF-GLYPH-U+0006]
q∈Q
bq = 0(B),
(2)
[PDF-GLYPH-U+0004]
q∈Q
bq = 1(B),
(3)
bq =
[PDF-GLYPH-U+0004]
q<q′
bq′.
And conversely {bq: q ∈Q} ⊆B satisfying (1), (2), and (3) determines an
element u ∈RB such that ∀q ∈Q
bq = [PDF-GLYPH-U+0001]ˆq ∈u[PDF-GLYPH-U+0002].
Now define the map h: M(E) →RB as follows. Given f ∈M(E), for
q ∈Q let
bq = {x ∈E: q < f(x)}/I .
It is readily checked that {bq: q ∈Q} satisfies (1)–(3) and so determines an
element uf of RB. We set h(f) = uf.
It is then not difficult to show that h is an algebra homomorphism with
kernel I. That h is onto RB may be seen by starting with u ∈RB and considering
the associated bq. If bq = Sq/I , then since {bq: q ∈Q} satisfies (1)–(3), we may
take the Sq to satisfy the conditions:
(1′)
[PDF-GLYPH-U+0007]
q∈Q
Sq = ∅,
(2′)
[PDF-GLYPH-U+0005]
q∈Q
Sq = E,
(3′)
Sq =
[PDF-GLYPH-U+0005]
q<q′
Sq′.
Now define fu : E →R by
fu(x) = sup{q: x ∈Sq}.
One checks that fu ∈M(E) and that
Sq = {x ∈E: q < fu(x)}.
From this it follows easily that h(fu) = u, establishing the surjectivity of h.
So h is an homomorphism of M(E) onto RB with kernel I. The theorem
follows.
A property ϕ(x) defined on E is said to hold almost everywhere if
{x ∈E: ¬ϕ(x)} has measure 0. Roughly speaking, truth in V (B) corresponds to
truth in V almost everywhere. A simple illustration of this is the following. Let us

```

## PDF page 172 | printed page 152

```text
152
BOOLEAN-VALUED ANALYSIS
say that f ∈M(E) is a correlate of u ∈RB if h(f) = u. Two measurable func-
tions f and g are then correlates of a single member in RB ifff = g almost
everywhere, that is, if {x ∈E: f(x) ̸= g(x)} has measure 0. Similarly, f and g
are correlates respectively of u, v for which u < v precisely when f < g holds
almost everywhere. The fact that the least upper bound principle for the real
numbers holds in V (B) then immediately yields the following.
Theorem 7.2 Let U be a nonempty set of measurable functions and suppose
that a measurable function f exists such that g ≤f almost everywhere for all
g ∈U. Then there exists a measurable function h such that :
1. g ≤h almost everywhere for all g ∈U;
2. if k is a measurable function such that g ≤k almost everywhere for all
g ∈U, then h ≤k almost everywhere.
Before stating our final result we require
Lemma 7.3 Suppose that V (B) |= u: ω →R(B) and, for each k ∈ω, uk ∈RB
satisfies [PDF-GLYPH-U+0001]uk = u(ˆk)[PDF-GLYPH-U+0002] = 1. For each k ∈ω, let fk be a correlate of uk and let g
be a correlate of v ∈RB. Then the following are equivalent:
• (fk)k∈ω converges to g almost everywhere
• V (B) |= limk→∞u(k) = v.
Proof We have
[PDF-GLYPH-U+0001] lim
k→∞u(k) = v[PDF-GLYPH-U+0002] = 1 ↔[PDF-GLYPH-U+0001]∀ε > 0∃n∀k ≥n|v −u(k)| < ε[PDF-GLYPH-U+0002] = 1
↔
[PDF-GLYPH-U+0007]
ε>0
[PDF-GLYPH-U+0005]
n
[PDF-GLYPH-U+0007]
k≥n
[PDF-GLYPH-U+0001]|v −u(k)| < ˆε[PDF-GLYPH-U+0002] = 1
↔
[PDF-GLYPH-U+0007]
ε>0
[PDF-GLYPH-U+0005]
n
[PDF-GLYPH-U+0007]
k≥n
[PDF-GLYPH-U+0001]|v −uk| < ˆε[PDF-GLYPH-U+0002] = 1
↔(
[PDF-GLYPH-U+0007]
ε>0
[PDF-GLYPH-U+0005]
n
[PDF-GLYPH-U+0007]
k≥n
{x : |g(x) −fk(x)| < ε})/I = E/I
↔{x : ∀ε > 0∃n∀k ≥n| |g(n) −fk(n)| < ε}/I = E/I
↔(fk)k∈ω converges to g almost everywhere.
Now suppose that V (B) |= u: ω →R(B) and, for each k ∈ω, uk ∈RB satisfies
[PDF-GLYPH-U+0001]uk = u(ˆk)[PDF-GLYPH-U+0002] = 1. For each k ∈ω, let fk be a correlate of uk. Let m = [PDF-GLYPH-U+0001]
k bk · #
nk
be a natural number in V (B), that is, nk ∈ω and {bk: k ∈ω} is a partition
of unity in B. Let v be the unique member of RB for which [PDF-GLYPH-U+0001]v = u(m)[PDF-GLYPH-U+0002] = 1.
Let {Sk: k ∈ω} ⊆S satisfy bk = Sk/I ; we may assume that {Sk: k ∈ω}
is a partition of E. Finally let g be the function on E whose restriction to
each Sk is fnk; it is not difficult to check that g is a correlate of v. From this,

```

## PDF page 173 | printed page 153

```text
BOOLEAN-VALUED MODELS FROM ALGEBRAS OF PROJECTIONS
153
Lemma 7.3, and the fact that the Bolzano–Weierstrass theorem holds for RB
with probability 1, one easily deduces the following.
Theorem 7.4 Suppose that g, f0, f1, . . . are measurable functions with |fk| < g
almost everywhere for all k. Then there exists a measurable function h such that
|h| < g almost everywhere and h is a Boolean-valued cluster function for (fk)k∈ω,
that is, for every ε > 0 and every m ∈ω there exist a measurable function e,
a sequence (nk)k∈ω of natural numbers, and a partition {Sk : k ∈ω} of E such
that
1. m ≤nk for every k;
2. for each k, the restriction of e to Sk is fnk;
3. |e(x) −h(x)| < ε almost everywhere.
Boolean-valued models built from algebras of projections
Let H be a (complex) Hilbert space, which will remain fixed throughout our
discussion: all operators, etc. will be assumed to be defined on H . Addition,
subtraction, and composition of operators will be denoted by +, −, and juxta-
position. The identity operator will be denoted by I and the zero operator by 0:
these are defined by Ix = x and 0x = 0. We recall that a projection is a bounded
self-adjoint operator P such that P 2 = P. The range ran(P) = {x: Px = x}
of a projection is a closed linear subspace of H ; conversely each closed linear
subspace S determines a projection PS such that S = ran(PS). The set P of
projections may be partially ordered by defining
P ≤Q ↔ran(P) ⊆ran(Q) ↔PQ = QP = P.
With this partial ordering P is a complete lattice in which I and 0 are the top
and bottom elements. Joins and meets in P are given by:
[PDF-GLYPH-U+0004]
i∈I
Pi = PS with S = closed linear span of
[PDF-GLYPH-U+0005]
i∈I
ran(Pi)
[PDF-GLYPH-U+0006]
i∈I
Pi = PS with S =
[PDF-GLYPH-U+0007]
i∈I
ran(Pi)
Each element P ∈P has a complement P c in P given by P c = I −P.1 Clearly
P cc = P and P ≤Q iffQc ≤P c. While the lattice P is not distributive, it is
orthomodular, that is, satisfies the following condition:
P ≤Q →P = Q ∧(P ∨Qc).
1We denote complementation in P by c in order to avoid confusion with the customary
use in functional analysis of the asterisk ∗to denote the adjoint operator.

```

## PDF page 174 | printed page 154

```text
154
BOOLEAN-VALUED ANALYSIS
The following laws governing complements of joins and meets in P obtain:
(
[PDF-GLYPH-U+0004]
i∈I
Pi)c = (
[PDF-GLYPH-U+0006]
i∈I
P c
i ),
(
[PDF-GLYPH-U+0006]
i∈I
Pi)c = (
[PDF-GLYPH-U+0004]
i∈I
P c
i ).
In sum, P is what is known as a complete orthomodular ortholattice.
Projections P, Q ∈P are said to commute if PQ = QP. The join and meet
of any commuting pair P, Q ∈P are given by
P ∨Q = P + Q −PQ,
P ∧Q = PQ.
It can be shown (Jauch 1968, section 5–7) that P, Q ∈P commute if and only
if they are compatible, that is,
P = (P ∧Q) ∨(P ∧Qc) and Q = (Q ∧P) ∨(Q ∧P c).
Clearly, P is compatible with Q iffP c is compatible with Q. It is easily seen that
the compatibility of P and Q is equivalent to the assertion that the sublattice
of P generated by {P, Q, P c, Qc} is a Boolean algebra. It follows that, for
any subset X of P consisting of pairwise compatible elements, the sublattice of
P generated by X ∪{P c: P ∈X } is a Boolean algebra. It can also be shown
(Jauch 1968, section 5–8), that, if P is compatible with each Qi for i ∈I, then
P is compatible with both [PDF-GLYPH-U+0003]
i∈I Qi and [PDF-GLYPH-U+0002]
i∈I Qi.
A complete Boolean projection algebra is a subset B of P such that
1. The elements of B are pairwise compatible, hence commute;
2. Both I and 0 are elements of B; if P
∈B, then P c ∈B, and if
{Pi: i ∈I} ⊆B, then both [PDF-GLYPH-U+0003]
i∈I Pi and [PDF-GLYPH-U+0002]
i∈I Pi ∈B.
Clearly, if B is a complete Boolean projection algebra, then (B, ≤) is a complete
Boolean algebra with top and bottom elements I and 0, respectively.
Lemma 7.5 Any set of pairwise commuting projections is contained in a
complete Boolean projection algebra.
Proof Let X be a set of pairwise commuting projections. Using Zorn’s lemma,
there is a maximal set M of pairwise commuting projections such that X ⊆M .
Then M is a complete Boolean projection algebra. For I and 0 are both compat-
ible with every member of M , hence members of M by maximality. If P ∈M ,
then P c is compatible with every member of M , hence also in M by maximality.
Finally, for any subset {Pi: i ∈I} of M , both [PDF-GLYPH-U+0003]
i∈I Pi and [PDF-GLYPH-U+0002]
i∈I Pi are compatible
with every member of M ; maximality again implies that they are both members
of M .
We shall need a few facts about spectral resolutions of self-adjoint operators.
A spectral family is a subset {Eλ: λ ∈R} of P satisfying the following

```

## PDF page 175 | printed page 155

```text
BOOLEAN-VALUED MODELS FROM ALGEBRAS OF PROJECTIONS
155
conditions:
(1)
[PDF-GLYPH-U+0006]
λ
Eλ = 0
(2)
[PDF-GLYPH-U+0004]
λ
Eλ = I
(3)
For any λ ∈R, Eλ =
[PDF-GLYPH-U+0006]
λ<µ
Eµ.
It follows from (3) that the members of a spectral family are pairwise commuting.
The spectral theorem (see Jauch 1968, section 4–3) asserts that corresponding
to each self-adjoint operator A there is a unique spectral family {Eλ: λ ∈R} for
which
A =
$
λdEλ.
The spectral family {Eλ: λ ∈R} is called the spectral resolution of A.
Let A and A′ be self-adjoint operators with spectral resolutions {Eλ: λ ∈R},
{E′
λ: λ ∈R}. A and A′ are said to be commutable if EλE′
µ = E′
µEλ for all
λ, µ. When A and A′ are bounded (continuous), commutability is equivalent to
commutativity: AA′ = A′A.
Now let B be a complete Boolean projection algebra. We define the closure
of B to be the set B comprising all those self-adjoint operators whose spectral
resolutions are included in B. Lemma 7.5 now immediately yields the following.
For any set X of self-adjoint pairwise commutable operators there exists a
complete Boolean projection algebra whose closure includes X .
We now fix a complete Boolean projection algebra B and turn our attention
to the B-valued universe V (B). The natural numbers and rational numbers in
V (B) are, respectively, mixtures of the form [PDF-GLYPH-U+0001]
k∈ω Pk · ˆnk or [PDF-GLYPH-U+0001]
k∈ω Pk · ˆqk with
{Pk: k ∈ω} a partition of unity in B and {nk: k ∈ω}, {qk: k ∈ω} sets of
natural and rational numbers, respectively. Straightforward rules for addition,
multiplication, and order of these mixtures apply. For example, if u = [PDF-GLYPH-U+0001]
k∈ω Pk ·
ˆnk and v = [PDF-GLYPH-U+0001]
k∈ω Qk · ˆmk, then, noting that {PkQj : k, j ∈ω} is a partition of
unity in B, we have
u + v =
[PDF-GLYPH-U+0004]
k,j∈ω
PiQj ·
[PDF-GLYPH-U+0001]
nk + mj, uv =
[PDF-GLYPH-U+0004]
k,j∈ω
PiQj · [PDF-GLYPH-U+0001]
nkmj, [PDF-GLYPH-U+0001]u < v[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0005]
{PkQj: nk < mj}.
In order to identify the field R(B) of real numbers in V (B) we again need to
specify a particular construction of R in V . In this situation we shall take R to
consist of the upper sections (now including end points, if any) of Dedekind cuts
in Q. Thus we shall define ‘r is a real number’ as
r ⊆Q ∧∃x ∈Q(x ∈r) ∧∃x ∈Q(x /∈r) ∧∀x ∈Q[x ∈r ↔∀y ∈Q(x < y →y ∈r)].
If we write the above formula as ϕ(r), then R(B) may be identified as the B-set
{r ∈PQ: ϕ(r)}(B), and RB as a core for this set.

```

## PDF page 176 | printed page 156

```text
156
BOOLEAN-VALUED ANALYSIS
Given u ∈RB, for q ∈Q define Pq ∈B to be [PDF-GLYPH-U+0001]ˆq ∈u[PDF-GLYPH-U+0002]. It is then
straightforward to verify that [PDF-GLYPH-U+0002]
q∈Q Pq
= 0,
[PDF-GLYPH-U+0003]
q∈Q Pq
= I, and for all
q ∈Q,
Pq = [PDF-GLYPH-U+0002]
q<s Ps. From this it follows easily that if for each λ ∈R we
define Eλ = [PDF-GLYPH-U+0002]
λ<q Pq, then {Eλ: λ ∈R} is a spectral family ⊆B.
Reciprocally, given a spectral family {Eλ: λ ∈R} ⊆B, define u ∈V (B) by
dom(u) = {ˆq: q ∈Q} and u(ˆq) = Pq. It is then easy to check that [PDF-GLYPH-U+0001]u ∈R(B)[PDF-GLYPH-U+0002] = 1.
The correspondence thus established between RB and spectral families ⊆B
is bijective. Since there is also a bijective correspondence between B and the
collection of spectral families ⊆B, it follows that there is a bijective corres-
pondence between RB and B. This may be informally expressed by saying that
the ‘interpretation’ of a real number in V (B) is a self-adjoint operator in B.
In Takeuti (1978) it is shown that the bijective correspondence between R(B)
and B is actually an isomorphism of R-algebras. There one will also find results
obtained by ‘interpreting’ in V (B) a number of theorems of elementary analysis.
For instance, in the case of the intermediate value theorem one obtains:
Suppose that f: R →R is continuous. Let A and B be commutable self-adjoint
operators with A ≤B, Y a self-adjoint operator commutable with both A and B
for which f(A) ≤Y ≤B. Then there exists a self-adjoint operator X commutable
with A, B, and Y such that A ≤X ≤B and Y = f(X).
Davis (1977) employs the Boolean-valued analysis just outlined to provide
a novel interpretation of the formalism of quantum theory. He points out
that in ‘quantizing’ a classical theory the symbols representing real quantit-
ies are replaced by symbols representing corresponding self-adjoint operators on
Hilbert space. The correspondence, for a complete Boolean projection algebra
B, between self-adjoint operators in B and B-valued real numbers suggests
that such projection algebras (or the associated Boolean-valued universes) be
regarded as reference frames with respect to which measurements may be made
of the observables corresponding to the operators in B. Under this inter-
pretation the B-valued real number correlated with a given observable A is
the value that would be obtained by measuring A with respect to the frame
B. The key point is that measurements must be made relative to a Boolean
frame, and, like inertial frames in relativity theory, there is no absolute such
frame.
In Davis’s interpretation, it is supposed that certain sentences of the language
of set theory are given, which express relationships among real physical quant-
ities. Some of these sentences will represent basic physical postulates, others
will express the result of a measurement. The correctness of such a sentence
σ as a description of reality is embodied in the assertion that V (B) |= σ for any
complete Boolean projection algebra B. The role played by a particular Boolean
frame may be grasped by analyzing a sentence expressing the fact that a real
quantity resulting from an interaction with some apparatus satisfies some con-
dition (an inequality, for instance). Such a sentence has the form p →q, where

```

## PDF page 177 | printed page 157

```text
BOOLEAN-VALUED MODELS FROM ALGEBRAS OF PROJECTIONS
157
p expresses the effect of the interaction and q the resulting condition.2 Then
p →q will hold, that is, V (B) |= p →q, in every Boolean frame B. But in
order to obtain from this the truth of q, that is, V (B) |= q, a frame B must be
chosen in which V (B) |= p. An appropriate choice of B will be determined by
the physics of the apparatus.
Quantities that can be measured simultaneously correspond to commuting
self-adjoint operators.3 Hence there is a complete Boolean projection algebra B
such that B contains all such operators: such an algebra B may be considered
a reference frame with respect to which the measurements are being made. In
the case of complementary quantities such as position and momentum, the cor-
responding operators do not commute and so there is no Boolean algebra B
such that B contains them both. A position measurement and a momentum
measurement can accordingly only be made with respect to distinct frames
of reference.
The notorious anomalies of quantum mechanics are thus seen to dissolve
under this interpretation. For example, consider the two-slit experiment. Here
we have two slits in front of a screen equipped with counters, and a beam of
particles that can reach the screen only by passing through one of the slits. The
pattern on the screen when both slits are open is, anomalously, found not to
coincide with the union of the patterns obtained when each is open separately.
The anomaly disappears when one observes that the Boolean frame associated
with opening both slits is different from that associated with the opening of a
single slit: the first frame corresponds to a momentum measurement, the second,
to a position measurement. In the case of the Einstein–Podolsky–Rosen paradox,
two particles A and B interact in such a way that the sum of their momenta
after the interaction is 0, so that a measurement of the momentum of A will
also yield the momentum of B. Such a measurement will accordingly not only
cause a ‘collapse’ of the state function of A, but also, and simultaneously, that
of B, which by this time may be very far away. Here the paradox is resolved as
follows. Let MA and MB be the momentum operators corresponding to A and B,
respectively, and let pA and pB represent their momenta at some time t. Then,
choosing an appropriate Boolean frame B for which B contains both A and B,
we know that V (B) |= pA + pB = 0. From this we deduce that MA + MB = 0:
it is the choice of the frame, not the measurement of pA, that guarantees the
result.
2Davis
offers
the
example
here
of
a
particle’s
presence
in
a
slit—a
‘position’
measurement—revealed by the action of a counter. In this case p may be taken to be the
statement ‘the counter clicks’ and q the statement ‘the particle was in the slit’.
3Note that since the transition from real quantities to self-adjoint operators is effected with
respect to a given frame, the fact that a particular observable is represented by some specific
operator must also be taken relative to a frame.

```

## PDF page 178 | printed page 158

```text
8
INTUITIONISTIC SET THEORY AND
HEYTING-ALGEBRA-VALUED MODELS
In this final chapter intuitionistic set theory is introduced and the idea of a
Boolean-valued model of classical set theory extended to that of a Heyting-
algebra-valued model of intuitionistic set theory.
Intuitionistic Zermelo set theory
The system IZ of intuitionistic Zermelo set theory is formulated in the language
L, subject to the axioms and rules of intuitionistic first-order logic. Arguments
in IZ will be presented informally; in particular we shall make use of the stand-
ard notations of classical set theory introduced previously: ∃y ∈x, ∀y ∈x,
{x: ϕ}, x ∪y, Px, ⟨x, y⟩, x ⊆y, ∅, 0, 1, 2, etc. The axioms of IZ are Extension-
ality, Separation, Union, Power set, Infinity (all as stated in the Prerequisites),
together with
Pairing
∀x∀y∃z∀w(w ∈z ↔w = x ∨w = y).
For any set A, PA is a complete Heyting algebra with operations ∪, ∩and ⇒,
where U ⇒V = {x: x ∈U →x ∈V }, and top and bottom elements A and ∅,
respectively.
We write {τ|ϕ} for {x: x = τ ∧ϕ}, where τ is a closed term; notice that
without the law of excluded middle we cannot conclude that {τ|ϕ} = ∅or {τ}.
From Extensionality we infer that {τ|ϕ} = {τ|ψ} iff(ϕ ↔ψ); thus, in particular,
the elements of P1 (recall that 1 = {0}) correspond naturally to truth values,
that is, propositions identified under equivalence. P1 is called the (Heyting)
algebra of truth values and is denoted by Ω. The top element 1 of Ωis usually
written true and the bottom element ∅as false.
We note that, in IZ, Ωplays the role of a subset classifier. That is, for each
set A, subsets of A are correlated bijectively to maps A →Ω. To wit, each
subset X ⊆A is correlated with its characteristic map χX : A →Ωgiven by
χX(x) = {0|x ∈X}; conversely each map f: A →Ωis correlated with the subset
f −1(1) of A.
Properties of Ωcorrespond to logical properties of the set theory. Recall,
for instance,
LEM (law of excluded middle) ϕ ∨¬ϕ
WLEM (weakened law of excluded middle) ¬ϕ ∨¬¬ϕ.

```

## PDF page 179 | printed page 159

```text
INTUITIONISTIC ZERMELO SET THEORY
159
LEM and WLEM correspond respectively to the properties
∀ω ∈Ω· ω = true ∨ω = false
∀ω ∈Ω· ω = false ∨ω ̸= false.
Calling a set A decidable if ∀x ∈A ∀y ∈A(x = y ∨x ̸= y), each of the
following is equivalent, in IZ, to LEM:
1. Every set is decidable.
2. Ωis decidable.
3. Ω= 2.
4. Membership is decidable: ∀x∀y(x ∈y ∨x /∈y).
5. ∀x(0 ∈x ∨0 /∈x).
6. (2, ≤) is well-ordered.
(To show that 6. implies LEM, observe that the least element of {0|ϕ} ∪{1} ⊆2
is either 0 or 1; if it is 0, ϕ must hold, and if it is 1, ϕ must fail.)
Using the axiom of infinity, the set N of natural numbers can be constructed as
usual. N is decidable and satisfies the familiar Peano axioms including induction,
but it is well-ordered only if LEM holds. In fact LEM also follows from the domino
principle for N:
ϕ(0) ∧∃n¬ϕ(n) →∃n[ϕ(n) ∧¬ϕ(n + 1)].1
To see this, take any formula ψ and define ϕ(n) to be the formula n = 0 ∨(n =
1∧ψ). Then clearly ϕ(0)∧∃n¬ϕ(n) holds, so we infer from the domino principle
that there is n0 for which ϕ(n) and ¬ϕ(n + 1), that is,
(∗)
n0 = 0 ∨(n0 = 1 ∧ψ)
and
¬(n0 + 1 = 1 ∧ψ)
whence
¬(n0 = 0 ∧ψ).
From this last we infer n0 = 0 →¬ψ, which, together; with (∗), gives ψ ∨¬ψ.
The notion of a function is defined as usual in IZ; we employ the standard
notations for functions. A choice function on a set A is a function f with domain
A such that f(a) ∈a whenever ∃x x ∈a. The axiom of choice AC is the assertion
that every set has a choice function. Remarkably, AC implies LEM; in fact it
1Here and in the sequel we shall use lower case letters m, n as variables ranging over N.

```

## PDF page 180 | printed page 160

```text
160
INTUITIONISTIC SET THEORY
is provable in IZ that if each doubleton has a choice function, then LEM holds
(and conversely).
To prove this, define U = {x ∈2: x = 0 ∨ϕ} and V = {x ∈2: x = 1 ∨ϕ},
and suppose given a choice function f on {U, V }. Writing a = f(U), b = f(V ),
we then have a ∈U, b ∈V , that is,
(a = 0 ∨ϕ) ∧(b = 1 ∨ϕ).
Hence
(a = 0 ∧b = 1) ∨ϕ
whence
a ̸= b ∨ϕ.
(∗)
But
ϕ →U = V →a = b,
so that
a ̸= b →¬ϕ.
This, together with (∗), gives ϕ ∨¬ϕ.
It can also be shown that the assertion any singleton has a choice function is
equivalent in IZ to the (intuitionistically invalid) ‘independence of premises’ rule,
ψ →∃x(x ∈A ∧ϕ(x))
∃x(ψ →x ∈A ∧ϕ(x)).
In classical set theory one proves the well-known Schr¨oder–Bernstein the-
orem: if each of two sets A and B can be injected into the other, then there
is a bijection between A and B. This is usually derived as a consequence of
the proposition
SB: for any set X and any injection f: X →X there is a bijection h:
X →Xsuch that h ⊆f ∪f −1, that is,
∀x ∈X[h(x) = f(x) ∨f(h(x)) = x].
In IZ this assertion implies (and so is equivalent to) LEM. Here is the proof.
Define, for any formula ϕ,
Nϕ = N −{0} ∪{0|ϕ}
f = {(n, n + 1): n ̸= 0} ∪{(0, 1)|ϕ}.

```

## PDF page 181 | printed page 161

```text
INTUITIONISTIC ZERMELO SET THEORY
161
Then f: Nϕ →Nϕ. Clearly
(∗)
1 ∈range(f) ↔0 ∈Nϕ ↔ϕ.
Now suppose given a bijection h: Nϕ →Nϕ such that
∀x ∈Nϕ[h(x) = f(x) ∨f(h(x)) = x].
If ϕ holds, then f is just the usual successor function on N(= Nϕ) and so
ϕ ∧h(n) = 0 →h(n) ̸= f(n) →1 = f(0) = f(h(n)) = n →n = 1,
whence
ϕ →h(1) = 0.
Thus
(∗∗)
h(1) ̸= 0 →¬ϕ
But
h(1) = f(1) ∨f(h(1)) = 1.
The first disjunct implies h(1) ̸= 0 and (∗∗) gives ¬ϕ. From the second disjunct
we infer 1 ∈range(f) and (∗) yields ϕ. Thus we have derived ϕ ∨¬ϕ.
Another theorem of classical set theory that, in IZ, implies the law of excluded
middle is the Stone Representation Theorem, namely, the assertion that every
Boolean algebra is isomorphic to a field of sets.2 To see this, observe first that,
in IZ, the Stone Representation Theorem implies the assertion
(∗)
In each Boolean algebra the intersection of the family of all
its prime filters is {1}.
For if B is a field of subsets of a set S, then, for each x ∈S, Fx = {X ∈B:
x ∈X} is a prime filter in B. If X ∈[PDF-GLYPH-U+001C]
x∈S Fx, then x ∈X for all x ∈X, whence
X = S. Therefore [PDF-GLYPH-U+001C]
x∈S Fx = {S} and so B has the property asserted in (∗). So
if the Stone Representation theorem holds (∗) obtains universally.
Now we show that (∗) implies LEM in IZ. For each Boolean algebra B, let
Prim(B) be the set of prime filters in B. Then [PDF-GLYPH-U+001C] Prim(B) = {1} and we have
(∗∗)
Prim(B) = ∅→B is trivial.
2Proved in Ch. 0.

```

## PDF page 182 | printed page 162

```text
162
INTUITIONISTIC SET THEORY
For if B is trivial, it has no filters, so that Prim(B) = ∅. Conversely, if
Prim(B) = ∅, then {1} = [PDF-GLYPH-U+001C] Prim(B) = ∩∅= B, so that B is trivial.
Now let ϕ be any formula, and define
Bϕ = {ω ∈Ω: ω = ϕ or ω = true}.
This is easily shown to be a Boolean algebra in which 0 = ϕ, 1 = true, meets are
conjunctions, joins are disjunctions, and the complement of ω is (ω →ϕ). Clearly
(∗∗∗)
Bϕ is trivial ↔ϕ.
Putting (∗∗) and (∗∗∗) together, we see that
ϕ ↔Prim(Bϕ) = ∅↔¬∃X X ∈Prim(Bϕ).
Thus ϕ is equivalent to a negated formula, and so satisfies the law of double
negation.
Since ϕ was arbitrary,
it follows that LDN, and hence LEM,
holds generally.
In ZFC one can prove the so-called order extension principle to the effect
that every partial ordering on a set can be extended to a total ordering.
We will show that, in IZ, this principle implies the intuitionistaically invalid
law ϕ →ψ ∨ψ →ϕ.
To prove this, we first observe that if U, V ⊆1, then
(∗)
(U = 1 →V = 1) ↔U ⊆V.
Now suppose that ≤is a total order on Ωextending ⊆. Then U ≤1 for all
U ∈Ω. Now
U ≤V ∧U = 1 →1 ≤V →V = 1,
whence, using (∗),
U ≤V →(U = 1 →V = 1) →U ⊆V.
We conclude that ≤and ⊆coincide. Accordingly, if ⊆could be extended to a
total order on Ω, ⊆would have to be a total order on Ωitself. But this is clearly
tantamount to the truth of ϕ →ψ ∨ψ →ϕ for arbitrary formulas ϕ and ψ.
The negation operation ¬ on propositions corresponds to the complement-
ation operation on Ω; we use the same symbol ¬ to denote the latter. This
operation of course satisfies
ω ⊆¬ω′ ↔ω ∩ω′ = false.

```

## PDF page 183 | printed page 163

```text
INTUITIONISTIC ZERMELO–FRAENKEL SET THEORY
163
Classically, ¬ also satisfies the dual law, viz.
¬ω ⊆ω′ ↔ω ∪ω′ = true.
But intuitionistically, this is far from being the case. Indeed, the assumption
that there exists any operation −: Ω→Ωsatisfying
−ω ⊆ω′ ↔ω ∪ω′ = true
implies (and so is equivalent to) LEM. For suppose such an operation existed.
Then
−true ⊆false ↔false ∪true = true,
so that −true ⊆false, whence −true = false. Next,
0 ∈−ω ∧0 ∈ω →0 ∈−ω ∧ω = true →0 ∈−true = false.
Since 0 /∈false, it follows that
0 ∈−ω →0 /∈ω →0 ∈¬ω,
and from this we infer that −ω ⊆¬ω. Since, obviously, ω ∪−ω = true, it then
follows that, for any ω, ω ∪¬ω = true, which is LEM.
Intuitionistic Zermelo–Fraenkel set theory
Intuitionistic Zermelo–Fraenkel set theory IZF is obtained by adding to IZ the
axioms of replacement and regularity3 (both as stated in Chapter 1).
It is to be expected that the many classically equivalent definitions of well-
ordering and ordinal become distinct within IZF. The definitions we give here
work reasonably well.
Definition
A set x is transitive if ∀y ∈x y ⊆x; an ordinal is a transitive
set of transitive sets. The class of ordinals is denoted by ORD and we use
(italic) letters α, β, γ, . . . as variables ranging over it. A transitive subset of
an ordinal is called a subordinal. An ordinal α is simple if ∀β ∈α γ ∈α
(β ∈γ ∨β = γ ∨γ ∈β).
3The version of the axiom of regularity we have been working with is commonly known as
the ∈-induction scheme. Classically, this is equivalent to the asserts that each nonempty set u
has a member x, which is ∈-minimal, that is, for which x ∩u = ∅. It is easy to see that this
implies LEM: an ∈-minimal element of the set {0|ϕ} ∪{1} is either 0 or 1; if it is 0, ϕ must
hold, and if it is 1, ϕ must fail; thus if foundation held we would get ϕ ∨¬ϕ.

```

## PDF page 184 | printed page 164

```text
164
INTUITIONISTIC SET THEORY
Thus, for example, the ordinals 1, 2, 3, . . . as well as the first infinite ordinal
ω to be defined below, are all simple. Every subordinal (hence every element) of
a simple ordinal is simple. But, in contrast with classical set theory, intuition-
istically not every ordinal can be simple, because the simplicity of the ordinal
{0, {0|ϕ}} implies ϕ ∨¬ϕ.
We next state the central properties of ORD.
Definition The successor α+ of an ordinal α is α ∪{α}; the supremum of a
set A of ordinals is [PDF-GLYPH-U+0015] A. The usual order relations are introduced on ORD:
α < β ↔α ∈β
α ≤β ↔α ⊆β.
It is now easily shown that successors and suprema of ordinals are again ordinals
and that
α < β ↔α+ ≤β
[PDF-GLYPH-U+0005]
A ≤β ↔∀α ∈Aα < β ≤γ →α < γ.
But straightforward arguments show that any of the following assertions (for
arbitrary ordinals α, β, γ) implies LEM: (i) α < β ∨α = β ∨β < α, (ii) α ≤
β ∨β ≤α, (iii) α ≤β →α < β ∨α = β, (iv) α < β →α+ < β ∨α+ = β,
(v) α ≤β < γ →α < γ.
Definition
An ordinal α is a successor if ∃β α = β+, a weak limit if
∀β ∈α ∃γ ∈α β ∈γ, and a strong limit if ∀β ∈α β+ ∈α.
Note that both the following assertions imply LEM: (i) every ordinal is zero,
a successor, or a weak limit, (ii) all weak limits are strong limits. Assertion (i)
follows from the observation that, for any formula ϕ, if the specified disjunction
applies to the ordinal {0|ϕ}, then ϕ ∨¬ϕ. As for assertion (ii), define
1ϕ = {0|ϕ}, 2ϕ = {0, 1ϕ}, β = {0, 1ϕ, 2ϕ, 2ϕ
+, 2ϕ
++, . . .}.
Then β is a weak limit, but a strong one only if ϕ ∨¬ϕ.
As in classical set theory, in IZF a connection can be established between
the class of ordinals and certain natural notions of well-founded or well-ordered
structure. Thus a well-founded relation on a set A is a binary relation which is
inductive, that is,
∀X ⊆A[∀x ∈A[∀y < x · y ∈X →x ∈X] →A ⊆X].
A well-founded relation has no infinite descending sequences and so is irreflexive.
Moreover, the usual proof may be given in IZF to justify definitions by recursion
on a well-founded relation, so that we can make the

```

## PDF page 185 | printed page 165

```text
HEYTING-ALGEBRA-VALUED MODELS
165
Definition If < is a well-founded relation on a set A, the associated rank
function ρ<: A →ORD is the (unique) function such that for each x ∈A,
ρ<(x) =
[PDF-GLYPH-U+0005]
{ρ<(y)+: y < x}.
When < is ∈restricted to an ordinal, it is easy to see that the associated
rank function is the identity.
To obtain a characterization of the order-types represented by ordinals we
make the
Definition
A
binary
relation
<
on
a
set
A
is
transitive
if
∀x ∈A∀y ∈A∀z ∈A(x < y ∧y < z →x < z),
and
extensional
if
∀x ∈A∀y ∈A[∀z(z < x ↔z < y) →x = y]. A well-ordering is a transitive,
extensional well-founded relation.
It is then easily shown that the well-orderings are exactly those relations iso-
morphic to ∈restricted to some ordinal. For it follows immediately from the
axioms of regularity and extensionality that the ∈-relation well-orders every
ordinal. And conversely, it is easy to prove by induction that the rank assigning
function on any well-ordering is an isomorphism.
Heyting-algebra-valued models
We now argue in ZFC. Suppose given a complete Heyting algebra H. We obtain
the H-valued universe4 V (H) by carrying out the definition of the Boolean-
valued universe V (B) with H in place of B; for sentences σ of L(H)—the
language obtained from L by adding a name for each member of V (H)—the
H-value [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]H (written simply [PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]) of σ in V (H) is defined analogously. Many
of the results established in Chapter 1 for V (B) hold, mutatis mutandis, for
V (H), and are proved in an analogous way: these include 1.7, Corollary 1.18,
Theorem 1.23 (based on Definition 1.22 of the canonical embeddingˆ, now from
V into V (H)), Lemma 1.25, Problem 1.29, and Lemma 1.31. Theorem 1.17 now
takes the form:
In V (H), all the axioms of intuitionistic first-order logic are true, and all its
rules of inference are valid. Clauses (i)–(vii) also continue to hold.
Theorem 1.33 now reads:
All the axioms of IZF are true in V (H).
4Although the definition of V (H) can carried out, and its properties established, in IZF,
this is more easily done in ZFC.

```

## PDF page 186 | printed page 166

```text
166
INTUITIONISTIC SET THEORY
Clearly LEM holds V (H) if and only if H is a Boolean algebra. Since AC
implies LEM, the former does not hold in any V (H) for which H is not a Boolean
algebra (for example, the algebra of opens of the space of real numbers). But,
interestingly, Zorn’s lemma is always valid in V (H). Here is a sketch of the
argument, in which Zorn’s lemma is taken in the form: any nonempty partially
ordered set in which every chain has a supremum also has a maximal element.
Thus suppose X, ≤X∈V (H) satisfy
V (H) |= ⟨X, ≤X⟩is a nonempty partially ordered set in which
every chain has a supremum.
Let Y be a core for X and define the relation ≤Y on Y by y ≤Y y′ ↔[PDF-GLYPH-U+0001]y ≤X
y′[PDF-GLYPH-U+0002] = 1; it is then easily verified that ⟨Y, ≤Y ⟩is a partially ordered set in which
every chain has a supremum. So, by Zorn’s lemma in V, Y has a maximal element
c. We claim that
[PDF-GLYPH-U+0001]c is a maximal element of X[PDF-GLYPH-U+0002] = 1.
(1)
To prove (1) we take any a ∈V (H) and define V
∈V (H) by dom(V ) =
dom(X) and
V (x) = [PDF-GLYPH-U+0001]x = a ∧x ∈X ∧c ≤X x[PDF-GLYPH-U+0002] ∨[PDF-GLYPH-U+0001]x = c[PDF-GLYPH-U+0002].
For x ∈dom(X). It is then readily verified that V (H) |= V is a chain in X; and
so (using Problem 1.29 for V (H)) there is v ∈Y for which
V (H) |= v is the supremum of V.
(2)
Since [PDF-GLYPH-U+0001]c ∈V [PDF-GLYPH-U+0002] = 1 it follows that [PDF-GLYPH-U+0001]c ≤X v[PDF-GLYPH-U+0002] = 1, whence c ≤Y v, so that v = c by
the maximality of c. This and (2) now yield [PDF-GLYPH-U+0001]a ∈V →a ≤X c[PDF-GLYPH-U+0002] = 1; and clearly
[PDF-GLYPH-U+0001]a ∈V →c ≤X x[PDF-GLYPH-U+0002] = 1. Therefore
[PDF-GLYPH-U+0001]a ∈V →a = c[PDF-GLYPH-U+0002] = 1.
(3)
It is easily verified that
[PDF-GLYPH-U+0001]a ∈X ∧c ≤X a[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]a ∈V [PDF-GLYPH-U+0002].
(4)
(3) and (4) yield [PDF-GLYPH-U+0001]a ∈X ∧c ≤X a[PDF-GLYPH-U+0002] ≤[PDF-GLYPH-U+0001]a = c[PDF-GLYPH-U+0002]; since this holds for arbitrary
a ∈V (H), (1) follows.
From the fact that Zorn’s lemma holds in every V (H) but AC does not we
may infer that, in IZF, the former does not imply the latter. In IZF Zorn’s lemma
is thus very weak, indeed so weak as to be entirely compatible with intuitionistic
logic. For more on this see Bell (1997).

```

## PDF page 187 | printed page 167

```text
FORCING IN HEYTING-ALGEBRA-VALUED MODELS
167
Forcing in Heyting-algebra-valued models and
independence in IZF
Let ⟨P, ≤⟩be a partially ordered set and for each p ∈P define Op = {q ∈P: q ≤
p}. Assign P the topology with base {Op: p ∈P} and write H for the complete
Heyting algebra O(P) of open sets in P. It is easy to see that the members
of O(P) are precisely the downward-closed subsets of P, that is, subsets U of
P satisfying x ∈U and y ≤x →y ∈U. The map p [PDF-GLYPH-U+0017]→Op is clearly order
preserving from P to H; let us agree to identify p with Op for each p ∈P, thus
identifying P as a subset of H.
We define the intuitionistic forcing relation ⊪between elements of P (which
will now be known as forcing conditions) and sentences of L(H) by
p ⊪σ iffp ≤[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002].
Intuitionistic forcing satisfies the following conditions:
• p ⊪σ ∧τ ↔p ⊪σ & p ⊪τ
• p ⊪σ ∨τ ↔p ⊪σ or p ⊪τ
• p ⊪σ →τ ↔∀q ≤p[q ⊪σ →q ⊪τ]
• p ⊪¬σ ↔∀q ≤p not q ⊪ϕ
• p ⊪∀xϕ ↔p ⊪ϕ(a) for every a ∈V (H)
• p ⊪∃xϕ ↔p ⊪ϕ(a) for some a ∈V (H).
Cohen forcing ⊩c (mentioned in Chapter 2) differs from intuitionistic forcing
only in that the clause for ∀is replaced by
p ⊩c ∀xϕ ↔∀q ≤p q ⊮c ϕ(a) for every a ∈V (H),
or equivalently
p ⊩c ∀xϕ ↔p ⊩c ¬∃x¬ϕ.
Clearly, V (H) |= σ iffp ⊪σ for all p, that is, truth in V (H) coincides with
the property of being universally forced. This explains the fact, puzzling at the
time of its introduction, that Cohen forcing satisfies intuitionistic rather than
classical rules: it reflects truth in the intuitionistic model V (O(P )), rather than
in the Boolean-valued model V (RO(P )).
In order to establish the independence of the axiom of choice from ZF we
constructed in Chapter 3 a Boolean-valued model containing an infinite but
Dedekind finite set. As we shall see, it is a much simpler task to construct a
Heyting-algebra-valued model of IZF with the same property.
Define the set K ∈V (H) by dom(K) = {ˆp : p ∈P} and K(ˆp) = Op. Then,
in V (H), K is a subset of ˆP and for p ∈P, [PDF-GLYPH-U+0001]ˆp ∈K[PDF-GLYPH-U+0002] = Op. Now consider the case
in which P is the opposite Nop of the totally ordered set N of natural numbers.

```

## PDF page 188 | printed page 168

```text
168
INTUITIONISTIC SET THEORY
Here the associated complete Heyting algebra H = O(Nop) is the family of all
upward-closed sets of natural numbers. In this case, as we shall see, the H-valued
set K is infinite and Dedekind finite in V (H).
To see this, first note that V (H) |= K ⊆ˆN and that V (H) |= ¬¬∀n ∈ˆN n ∈K.
But then, working in V (H), if ∀n ∈ˆN n ∈K, then K is not finite, so if K were
finite, then ¬∀n ∈ˆN n ∈K, and so ¬¬∀n ∈ˆN n ∈K yields the nonfiniteness
of K.
But, in V (H), K is Dedekind finite. For (again working in V (H)), if K were
Dedekind infinite (i.e. if there existed an injection of ˆN into K), then the sentence
∀x ∈K∃y ∈K x < y would also have to hold in V (H). But calculating the truth
value of that sentence gives:
[PDF-GLYPH-U+0001]∀x ∈K∃y ∈Kx < y[PDF-GLYPH-U+0002] =
[PDF-GLYPH-U+0007]
m∈Nop
[Om ⇒
[PDF-GLYPH-U+0005]
n∈Nop
[On ∩[PDF-GLYPH-U+0001] ˆm < ˆn[PDF-GLYPH-U+0002] ]
=
[PDF-GLYPH-U+0007]
m
[Om ⇒
[PDF-GLYPH-U+0005]
m<n
On]
=
[PDF-GLYPH-U+0007]
m
[Om ⇒Om+1]
=
[PDF-GLYPH-U+0007]
m
Om+1
= ∅
Therefore ∀x ∈K∃y ∈Kx < y is false in V (H) and so K is not Dedekind infinite.
Many other independence results from IZF can be established by the use
of Heyting-algebra-valued models. For example, in Fourman and Hyland (1979)
such models are presented in which
• the sets of Cauchy and Dedekind real numbers fail to coincide
• the field of complex numbers fails to be algebraically closed
• every function from R to R is continuous.

```

## PDF page 189 | printed page 169

```text
APPENDIX
BOOLEAN AND HEYTING ALGEBRA-VALUED MODELS AS
CATEGORIES
In this appendix we provide a brief introduction to category theory1 and describe
how a Boolean and Heyting algebra-valued model can be viewed as a category
of a particularly significant kind known as a topos.
Categories and functors
A category C is determined by first specifying two classes Ob(C ), Arr(C )—
the collections of C -objects and C -arrows. These collections are subject to the
following axioms:
• Each C -arrow f is assigned a pair of C -objects dom(f), cod(f) called the
domain and codomain of f, respectively. To indicate the fact that C -objects
X and Y are respectively the domain and codomain of f we write f: X →Y
or X
f
−→Y . The collection of C -arrows with domain X and codomain Y is
written C (X, Y ).
• Each C -object X is assigned a C -arrow 1X: X →X called the identity arrow
on X.
• Each pair f, g of C -arrows such that cod(f) = dom(g) is assigned an arrow
g ◦f: dom(f) →cod(g) called the composite of f and g. Thus if f: X →Y
and g: Y →Z then g ◦f: X →Z. We also write X
f
−→Y
g
−→Z for g ◦f.
Arrows f, g satisfying cod(f) = dom(g) are called composable.
• Associativity law. For composable arrows (f, g) and (g, h), we have
h ◦(g ◦f) = (h ◦g) ◦f.
• Identity law. For any arrow f: X →Y , we have f ◦1X = f = 1Y ◦f.
As a basic example of a category, we have the category Set of sets whose objects
are all sets and whose arrows are all maps between sets (strictly, triples (f, A, B)
with domain(f) = A and range (f) ⊆B.) Other examples of categories are the
category of groups, with objects all groups and arrows all group homomorphisms
and the category of topological spaces with objects all topological spaces and
arrows all continuous maps. Categories with just one object may be identified
with monoids, that is, algebraic structures with an associative multiplication
and an identity element.
1Useful accounts of category theory include Mac Lane (1971) and McLarty (1992).

```

## PDF page 190 | printed page 170

```text
170
APPENDIX
We list some basic category-theoretic definitions:
Commutative diagram
(in category)
Diagram of objects and arrows such that the
arrow obtained by composing the arrows of any
connected path depends only on the endpoints of
the path.
Initial object
Object 0 such that, for any object X, there is a
unique arrow 0 →X (e.g. ∅in Set)
Terminal object
Object 1 such that, for any object X, there is a
unique arrow X →1 (e.g. {0} in Set)
Element of an object X
Arrow 1 →X (in Set, member of X )
Monic arrow X ↣Y
Arrow f: X →Y such that, for any arrows
g, h: Z →X, f ◦g = f ◦h ⇒g = h (in Set,
one–one map)
Epic arrow X ↠Y
Arrow f: X →Y such that, for any arrows g, h:
Y →Z, g ◦f = h ◦f ⇒g = h (in Set, onto map)
Isomorphism X ∼= Y
Arrow f: X →Y for which there is g: Y →X
such that g ◦f = 1X, f ◦g = 1Y (in Set, bijection)
Decomposition of arrow
f: A →B
Pair of arrows with A
k
−→C
m
−→B with k epic,
m monic and m ◦k = f. The decomposition
(k, m) of f is said to be unique (up to
isomorphism if for any decomposition
A
k′
−→C′ m′
−→B of f there is an isomorphism
i: C ∼= C′ such that the diagram
C
B
A
k[PDF-GLYPH-U+0001]
m[PDF-GLYPH-U+0001]
C
k
m
commutes. (In Set, the decomposition of a map
f: A →B is the pair consisting of f considered as
a surjection onto f[A] and the insertion map of
f[A] into B.)
Image of arrow
f: A →B
Monic m in a unique decomposition (k, m) of f
Amenable category
Category in which every arrow admits a unique
decomposition

```

## PDF page 191 | printed page 171

```text
APPENDIX
171
Product of objects
X, Y
Object X × Y with arrows (projections)
X
π1
←−X × Y
π2
−→Y such that any diagram
·
f g
can be uniquely completed to a
commutative diagram
•
f
g
<f,g>
[PDF-GLYPH-U+0001]1
[PDF-GLYPH-U+0001]2
X
X×Y
←
→Y
(In Set, Cartesian product of sets with projection
maps.)
Product of arrows
f1: X1 →Y1
f2: X2 →Y2
Unique arrow f1 × f2: X1 × X2 →Y1 × Y2 making
the diagram
X1×X2
f1 × f2
[PDF-GLYPH-U+0001]2
[PDF-GLYPH-U+0001]1
Y1
f1
f2
Y1×Y2
Y2
X1
X2
[PDF-GLYPH-U+0001]1[PDF-GLYPH-U+0001]
[PDF-GLYPH-U+0001]2[PDF-GLYPH-U+0001]
commute. That is, f1 × f2 = ⟨f1 ◦π1, f2 ◦π2⟩.
Coproduct of objects
X, Y
Object X + Y together with a pair of arrows
X
σ1
−→X + Y
σ2
←−Y such that for any pair of
arrows X
f
−→A
g
←−B, there is a unique arrow
X + Y
f+g
−→A such that the diagram
f
g
f + g
A
s1
s2
X
X× Y←
→
Y
commutes. (In Set, disjoint union with insertions
maps.)
Pullback diagram or
square
Commutative diagram of the form
C
g
A
f
B
D

```

## PDF page 192 | printed page 172

```text
172
APPENDIX
such that for any commutative diagram
B
♦
g
A
D
f
there is a unique ♦
!
−→C such that
♦
 !
C
B
g
A
D
commutes.
f
(In Set, C is {⟨x, y⟩: f(x) = g(y)}. If D=1, then
C is A × B; if A ⊆D and f is the insertion map,
then C is g−1[A]; if A, B ⊆D and f and g are
insertions, then C is A ∩B.
Equalizer of pair of
arrows
f
[PDF-GLYPH-U+0001]
•
g
Arrow ♦
e
−→■such that f ◦e = g ◦e and, for any
arrow ▲
e′
−→■such that f ◦e′ = g ◦e′ there is a
unique ▲
u
−→♦such that
→
e[PDF-GLYPH-U+0001]
e
u
[PDF-GLYPH-U+0002]
[PDF-GLYPH-U+0001]
commutes. (In Set, {x: f(x) = g(x)} with
insertion map.)
Subobject of an object X
Pair (m, Y ), with m a monic arrow Y ↣X
Truth value object or
subobject classifier
Object Ωtogether with arrow true: 1 →Ωsuch
that every monic m: • ↣♦(i.e. subobject of ♦)
can be uniquely extended to a pullback diagram
of the form
[PDF-GLYPH-U+0002]
Ω
•
1
m
t
χ(m)

```

## PDF page 193 | printed page 173

```text
APPENDIX
173
χ(m) is the characteristic arrow of m. (In Set, Ω
is the set 2 = {0, 1} t is 1 and χ(m) is the
characteristic function of the image of m.) For
any object A, χ(1A) is written TA.
Power object of an
object X.
An object PX together with an arrow
(evaluation) eX: X × PX →Ωsuch that, for any
f: X × PX →Ω, there is a unique arrow
Y →PX such that
f
1X × f
eX
X ×Y
Ω
X ×PX
commutes. (In Set, PX is the power set of X and
eX the characteristic function of the membership
relation between X and PX.)
Exponential object of
objects Y, X
An object Y X, together with an arrow
ev: X × Y X →Y such that, for any arrow
f: X × Z →Y there is a unique arrow
ˆf: Z →Y X—the exponential transpose of
f—such that the diagram
f
X ×YX
ev
Y
1X × f
X ×Z
commutes. In Set, Y X is the set of all maps
X →Y and ev is the map that sends (x, f)
to f(x).
Product of indexed set
{Ai: i ∈I} of objects
Object %
i∈I Ai together with arrows
%
i∈I Ai
πi
−→Ai (i ∈I) such that, for any arrows
fi: B →Ai (i ∈I) there is a unique arrow
h: B −→%
i∈I Ai such that, for each i ∈I, the
diagram
h
[PDF-GLYPH-U+0002]
B →
Ai
[PDF-GLYPH-U+0001]i
fi
Ai
i  I
commutes.

```

## PDF page 194 | printed page 174

```text
174
APPENDIX
Coproduct of indexed
set {Ai: i ∈I} of
objects
Objects &
i∈I Ai together with arrows
Ai
σi
−→&
i∈I Ai (i ∈I) such that, for any arrows
fi: Ai →B (i ∈I) there is a unique arrow
h: &
i∈I Ai −→B such that, for each i ∈I, the
diagram
si
i  I
[PDF-GLYPH-U+0002]
→
Ai
Ai
fi
h
B
commutes.
A category is said to satisfy the axiom of choice if for any epic f: A ↠B
there is a (necessarily monic) g: B →A such that f ◦g = 1B. We assume that
the axiom of choice holds in Set: this is equivalent to assuming the axiom of
choice in any of its usual forms.
A functor F: C →D between two categories C and D is a map that ‘preserves
commutative diagrams’, that is, assigns to each C -object A a D-object FA and
to each C -arrow f: A →B a D-arrow Ff: FA →FB in such a way that:
A
FA
f
Ff
B
FB
A
1 A
FA
1 FA
F(1A)=1FA
f
Ff
•
•
•
•
F (g [PDF-GLYPH-U+0003]f ) = Fg [PDF-GLYPH-U+0003]Ff
h
g
Fh
Fg
•
•
commutes
commutes

```

## PDF page 195 | printed page 175

```text
APPENDIX
175
Two functors F: C →D and G: D →E can obviously be composed to yield
a functor GF: C →E . Associated with each category C we have the evident
identity functor 1C : C →C .
Given functors F, G: C →D, a natural transformation between F and G
is a map η from the objects of C to the arrows of D satisfying the following
conditions.
• For each object A of C , ηA is an arrow FA →GA in D
• For each arrow f: A →A′ in C , the diagram
[PDF-GLYPH-U+0002]A
FA
Ff
Gf
[PDF-GLYPH-U+0002]A[PDF-GLYPH-U+0001]
FA[PDF-GLYPH-U+0001]
GA
GA[PDF-GLYPH-U+0001]
commutes.
When each ηA is an isomorphism we say that η is a natural isomorphism between
F and G and that F and G are naturally isomorphic, written F ∼= G.
A functor F: C →D is an equivalence if it is ‘an isomorphism up to
isomorphism’, that is, if it is
• faithful: Ff = Fg ⇒f = g.
• full: for any h: FA →FB there is f: A →B such that h = Ff.
• dense: for any D-object B there is a C -object A such that B ∼= FA.
An equivalence F: C →D can also be characterized as a functor admitting a
quasi-inverse, that is, for which there exists a functor G: D →C such that
FG and GF are naturally isomorphic to the identity functors on D and C
respectively. Two categories are equivalent, written ≃, if there is an equivalence
between them. Equivalence is the appropriate notion of ‘identity of form’ for
categories.
Toposes
A category is cartesian closed if it has a terminal object, as well as products
and exponentials of arbitrary pairs of its objects. It is finitely complete if it
has a terminal object, products of arbitrary pairs of its objects, and equalizers.
An (elementary) topos2 is a category possessing a terminal object, products,
a truth-value object, and power objects. It can be shown that every topos is
2Accounts of topos theory may be found in Bell (1988), Goldblatt (1979), Johnstone (1977)
and (2002), Lambek and Scott (1986), Mac Lane and Moerdijk (1992), and McLarty (1992).
See also Mac Lane (1975).

```

## PDF page 196 | printed page 176

```text
176
APPENDIX
cartesian closed, finitely complete, and amenable. The basic example of a topos
is Set: its terminal and truth-value objects, products and power objects have
been identified above.
Here are some further examples of toposes.
Set→: topos of sets varying over two possible states 0 (then), 1 (now), with
0 ≤1. An object X here is a pair of sets X0, X1 together with a ‘transition’ map
p: X0 →X1. An arrow F: X →Y is a pair of maps f0: X0 →Y0, f1: X1 →Y1
compatible with the transition maps in the sense that the diagram
p
X0
X1
f0
f1
q
Y0
Y1
commutes.
Notice that the truth value object Ωin Set→has 3 (rather than 2) elements.
For if (m, X) is a subobject of Y in Set→, then we may take X0 ⊆Y0, X1 ⊆
Y1, f0 and f1 identity maps, and p to be the restriction of q to X0. Then for any
y ∈Y there are three possibilities, as depicted below: (0) q(y) ∈X1 and y /∈X0,
(1) y ∈X0, and (2) q(y) /∈X1.
2
2
1
0
1
1
Y0
Y1
X0
X1
So if 2 = {0, 1} and 3 = {0, 1, 2} we take Ωto be the variable set 3 →2 with
0 [PDF-GLYPH-U+0017]→1, 1 [PDF-GLYPH-U+0017]→1, 2 [PDF-GLYPH-U+0017]→2.
More generally, we may consider sets varying over n, or ω, or any totally
ordered ‘number’ of stages. In each case there is ‘one more’ truth value than
stages: ‘truth’ = ‘time’ + 1.
Still more generally, we may consider the category SetP of sets varying over
partially ordered set P. As objects this category has functors P →Set, that is,
maps F which assign to each p ∈P a set F(p) and to each p, q ∈P such that

```

## PDF page 197 | printed page 177

```text
APPENDIX
177
p ≤q a map Fpq: F(p) →F(q) satisfying:
Fpq
p[PDF-GLYPH-U+0003]q [PDF-GLYPH-U+0003]r implies that
F(p)
F(q)
Fpr
Fqr
F(r)       commutes;
and
Fpp is the identity map on F(p).
An arrow η: F →G in SetP is a natural transformation between F and G, in
this case, an assignment of a map ηp: F(p) →G(p) to each p ∈P in such a way
that, whenever p ≤q, the diagram
Fpq
F(p)
F(q)
[PDF-GLYPH-U+0002]p
[PDF-GLYPH-U+0002]q
Gpq
G(p)
G(q) commutes.
The truth-value object Ωin SetP is determined as follows. A subset U of
Op = {q ∈P : p ≤q} such that q ∈U, r ≥q ⇒r ∈U is said to be upward closed
over p. Then
Ω(p) = family of all upward-closed sets over p,
Ωpq(U) = U ∩Oq for p ≤q, U ∈Ω(p).
The terminal object 1 in SetP is the functor on P with constant value 1 = {0}
and true: 1 →Ωhas truep(0) = Op for each p ∈P.
Objects in SetP op, where P op is the partially ordered set obtained by reversing
the order on P, are called presheaves on P. If F is a presheaf on P, x ∈F(p),
and q ≤p, we write x↾F q for Fpq(x).
Now let H be a complete Heyting algebra. A presheaf F on H is a sheaf if
whenever p = [PDF-GLYPH-U+0003]
i∈I pi in H and si ∈F(pi) for all i ∈I satisfy si↾F (pi ∩pi) =
sj↾F (pi ∩pj) for all i, j ∈I, then there is a unique s ∈F(U) such that s↾F pi = si
for all i ∈I. The category Shv(H) of sheaves on H has as objects the sheaves on

```

## PDF page 198 | printed page 178

```text
178
APPENDIX
H and as arrows and as arrows all arrows between these objects qua presheaves.
It can be shown that Shv(H) is a topos.
In any topos E the truth-value object Ωsupports natural arrows representing
the familiar logical operations ∧, ∨, ⇒, ¬. To wit,
∧: Ω× Ω→Ωis the characteristic arrow of the monic
< true, true > : 1 →Ω× Ω;
∨: Ω× Ω→Ωis the characteristic arrow of the
image of Ω+ Ω
<TΩ,1Ω>+<1Ω,TΩ>
−−−−−−−−−−−−−→Ω+ Ω;
¬: Ω→Ωis the characteristic arrow of false : 1 →Ω, where false is the
characteristic arrow of the monic 0 →1;
⇒Ω× Ω→Ωis the characteristic arrow of the equalizer of the pair
of arrows π1, ∧: Ω× Ω→Ω.
It can then be shown that with these operations Ωis an ‘internal Heyting
algebra’ in E in the sense the diagrams in E representing equations character-
izing Heyting algebras (see Ch. 0) all commute. For example, the commutative
diagram corresponding to the equation x ∧(x ⇒y) is
Ω× Ω → Ω× (Ω× Ω) → Ω×Ω
π1× 1Ω× Ω
1Ω×⇒
Ω
^
^
Ωis an internal Boolean algebra in E if ¬ ◦¬ = 1Ω. A topos satisfying this
condition is called Boolean; clearly the topos Set is Boolean. It is not difficult
to show that each of the following conditions on a topos E are necessary and
sufficient for it to be Boolean: (i) 1 + 1
true+false
−−−−−−→Ωis an isomorphism; (ii) all
subobjects in E have complements, that is, given a monic U ↣X there is a
monic V ↣X such that U + V →X is an isomorphism.
Diaconescu’s theorem asserts that any topos in which the axiom of choice
holds is Boolean. This is the category-theoretic form of the fact (proved in Ch. 8)
that in intuitionistic set theory the axiom of choice implies the law of excluded
middle.

```

## PDF page 199 | printed page 179

```text
APPENDIX
179
Recall that an element of an object X is an arrow 1 →X. If E is a topos, the
set Ω(E ) of elements of Ωin E can be assigned a partial ordering ≤by defining
u ≤v iffu ∧v = u; more exactly, if the diagram
1
Ω
Ω
u
^
<u, v>
commutes. From the fact that Ωis an internal Heyting algebra it follows that,
with this partial ordering, Ω(E ) is a Heyting algebra, the algebra of external
truth values of E . When E is Boolean, Ω(E ) is a Boolean algebra.3 A topos is
bivalent if its algebra of external truth values contains just the two elements true
and false. Clearly Set is bivalent.
Ω(E ) is complete when E admits arbitrary coproducts of 1, that is, if for
any set I the I-indexed coproduct &
I 1 exists in E . Although not every topos
satisfies this condition, it is satisfied by all the toposes we have mentioned. Here
is a table giving Ω(E ) for various toposes E .
E
Ω(E )
Set
2
SetP op
O(P) with P assigned order topology
Shv(H)
H
Boolean and Heyting algebra-valued-models as toposes
If H is a complete Heyting algebra, the ‘topos of sets constructed within V (H)’ is
also a topos. More precisely, we obtain a topos Set(H) from V (H) in the following
way. First, we identify elements u, v of V (H) when [PDF-GLYPH-U+0001]u = v[PDF-GLYPH-U+0002] = 1. The objects of
the category Set(H) are the (thus identified) objects of V (H) and the arrows of
Set(H) are those (identified) objects f of V (H) for which [PDF-GLYPH-U+0001]f is a function[PDF-GLYPH-U+0002] = 1.
Composition and identity arrows are defined in the obvious way. Now it is easy
to derive in IZF the assertion that Set is a topos with subject classifier P1. So
since the axioms of IZF are all true in V (H), it follows that Set(H) is a topos
with subobject classifier Ω= P (H)(ˆ1).4 For each set I, the H-valued set ˆI is
readily shown to be the I-indexed copower of 1 in Set(H). Elements of Ωin
Set(H) correspond to the u ∈V (H) for which [PDF-GLYPH-U+0001]u ∈Ω[PDF-GLYPH-U+0002] = [PDF-GLYPH-U+0001]u ⊆ˆ1[PDF-GLYPH-U+0002] = 1H. These are
in turn correlated with the elements of H via the map u [PDF-GLYPH-U+0017]−→[PDF-GLYPH-U+0001]ˆ0 ∈u[PDF-GLYPH-U+0002]. Thus the
3The converse, however, does not hold.
4Here P (H) is the power set operation in V (H).

```

## PDF page 200 | printed page 180

```text
180
APPENDIX
algebra of external truth values of Set(H) is isomorphic to H. If B is a complete
Boolean algebra, Set(B) is a Boolean topos whose algebra of external truth values
is isomorphic to B.
There is an alternative description of the topos Set(H) employing the notion
of an H-set. This defined to be a set X equipped with an ‘H-valued equality
relation’ δ: X × X →H satisfying
δ(x, x′) = δ(x′, x)
δ(x, x′) ∧δ(x′, x′′) ≤δ(x, x′′).
We shall write [PDF-GLYPH-U+0001]x = x′[PDF-GLYPH-U+0002] for δ(x, x′). The category SetH of H-sets has as objects all
H-sets; its arrows are ‘H-valued functional relations’. That is, an arrow between
two H-sets X and Y is a function f: X × Y →H satisfying
[PDF-GLYPH-U+0001]x = x′[PDF-GLYPH-U+0002] ∧f(x, y) ≤f(x′, y)
f(x, y) ∧[PDF-GLYPH-U+0001]y = y′[PDF-GLYPH-U+0002] ≤f(x, y′)
f(x, y) ∧f(x, y′) ≤[PDF-GLYPH-U+0001]y = y′[PDF-GLYPH-U+0002]
[PDF-GLYPH-U+0004]
y∈Y
f(x, y) = [PDF-GLYPH-U+0001]x = x[PDF-GLYPH-U+0002].
Given two arrows (X, δ)
f
−→(Y, ε) and (Y, ε)
g
−→(Z, η), the composite
(X, δ)
g◦f
−→(Z, η), is defined by
(g ◦f)(x, z) =
[PDF-GLYPH-U+0004]
y∈Y
f(x, y) ∧g(y, z),
while the identity arrow on (X, δ) is just δ.
It can be shown that SetH and Set(H) are equivalent categories. With each
u ∈V (H) we associate the H-set ˜u = (dom(u), δu) where δu(x, y) = [PDF-GLYPH-U+0001]x ∈
u ∧x = y[PDF-GLYPH-U+0002]; and if u, v and f ∈V (H) are such that V (H) |= f: u →v, we obtain
an arrow ˜f: ˜u →˜v by defining ˜f(x, y) = [PDF-GLYPH-U+0001]f(x) = y[PDF-GLYPH-U+0002]. This procedure yields a
functor from Set(H) to SetH.
Now let (X, δ) be an H-set. For each x ∈X define ˙x ∈V (H) by dom( ˙x) =
{ˆz: z ∈X} and ˙x(ˆz) = δ(x, z). Define X† ∈V (H) by dom(X†) = { ˙x: x ∈X} and
X†( ˙x) = δ(x, x). X† is taken to correspond to X. Given an arrow f: (X, δ) →
(Y, ε) in SetH, define f † ∈V (H) by dom(f †) = {⟨˙x, ˙y⟩(H): x ∈X, y ∈Y } and
f †(⟨˙x, ˙y⟩(H)) = f(x, y). It is not difficult to verify that V (H) |= f †: X† →Y †.
This gives us a functor from SetH to Set(H).
It can then be verified that these two functors are quasi-inverse and so define
an equivalence between Set(H) and SetH.
It can also be shown (Higgs 1973, Fourman and Scott 1979) that Shv(H) and
SetH are equivalent categories. Accordingly all three toposes Set(H), SetH, and
Shv(H) are equivalent, yielding two alternative ways of describing (the topos of)

```

## PDF page 201 | printed page 181

```text
APPENDIX
181
H-valued sets: as sheaves on H, or as sets equipped with an H-valued equality
relation.
Finally, we mention that toposes of Heyting-algebra (or Boolean-valued) sets
can be characterized in categorical terms. A collection G of objects of a category
is called a generating class if for any pair of distinct arrows f, g: A →B there
is a member G of G and an arrow h: G →A such that f ◦h ̸= g ◦h. A topos
is said to be extensional if {1} is a generating class, and subextensional if the
collection of subobjects of 1 is a generating class, that is, if for any distinct
arrows f, g: A →B there is a subobject U ↣1 and an arrow h: U →A
such that f ◦h ̸= g ◦h. It can then be shown (see Bell 1988) that a topos is
equivalent to a topos of the form Set(H) if and only if it is subextensional and
admits arbitrary set indexed coproducts of 1. Moreover, a topos is equivalent to
a topos of the form Set(B), for a complete Boolean algebra B, if and only if it
admits arbitrary coproducts of 1 and satisfies the axiom of choice. For Set itself
we have the following characterization: to be equivalent to Set it is necessary and
sufficient that it be extensional and admit arbitrary coproducts of 1, or that it be
bivalent and satisfy the axiom of choice, and admit arbitrary coproducts of 1.
The role of the axiom of choice in characterizing the classical universe of sets
in categorical terms is quite striking.

```

## PDF page 202 | printed page 182

```text
HISTORICAL NOTES
Chapter l
Boolean-valued models of set theory were first introduced by Scott
and Solovay (see Scott 1967) and Vopˇenka (1967). Most of the results of this
chapter appear in Scott (1967).
Chapter 2
The method of forcing was invented by Cohen, who also proved the
independence of the axiom of constructibility and of the continuum hypothesis.
Corollary 2.13 is due to Solovay (1965). The Boolean-valued versions of these
results appear in Scott (1967) and Vopˇenka (1967). For an approach to forcing
closely related to the Boolean-valued one given here, see Shoenfield (1971).
The results in Problems 2.14–2.16 appear in Scott (1967). Problem 2.20 is
due to Solovay (1963).
Chapter 3
The independence of the axiom of choice from ZF was established
by Cohen in 1963 (see Cohen 1966). The Boolean-valued version may be found
in Scott (1967) and Vopˇenka (1967). Corollary 3.9. is due to Feferman (1965).
Chapter 4
The construction of generic extensions of models of set theory is due
to Cohen (1963, 1964); the approach in this chapter is closely related to that of
Shoenfield (1971). Theorems 4.6, 4.15, and 4.19 are from Bell (1976a). The result
in Problem 4.27 is due to Mansfield and Dawson (1976), that in Problem 4.33
is due to Bell (1976), Problem 4.36 is due to Solovay (1970), Problem 4.37 is
due to Solovay (v. also Grigorieff1975), Problems 4.38 and 4.39 due to Vopˇenka
(v. Grigorieff1975).
Chapter
5
The concept of a collapsing algebra,
Corollary 5.2,
and
Problems 5.3 and 5.4 are due to Levy. The result in Problem 5.5 is due to Levy
and Solovay (1967). Results 5.8–5.12 are due to Ellentuck (1976). Theorem 5.13
is a result of Solovay (1966) and Theorem 5.14 by Kripke (1967). Problem 5.16
is due to Bell (1975).
Chapter 6
The formulation of Souslin’s hypothesis in terms of trees is
due to Miller (1943). The independence of SH from ZFC is due independ-
ently to Jech (1967) and Tennenbaum (1968): I have elected to present the
latter’s construction. The relative consistency of SH is due to Solovay and
Tennenbaum (1971), on which my exposition is largely based. Martin’s axiom
(which was independently formulated by Rowbottom) makes its first appear-
ance in print in Martin and Solovay (1970), where various applications are
presented. Problems 6.35–6.37 are drawn from Solovay and Tennenbaum (1971),
and Problem 6.38 from Bell (1983).
Chapter 7
Boolean-valued analysis using measure algebras was introduced by
Scott (1969), and later developed by Takeuti. An account of the latter’s work

```

## PDF page 203 | printed page 183

```text
HISTORICAL NOTES
183
in this area appears in Takeuti (1978): this has provided the source of much
of my exposition. There also the use of algebras of projections as a basis for
Boolean-valued analysis is introduced and extensively developed. The idea of
interpreting quantum theory in terms of the correspondence between projection-
algebra-valued real numbers and commuting self-adjoint operators is due to
Davis (1977).
Chapter 8
Intuitionistic set theory has emerged at the hands of a number of
people: for my exposition I have chosen Grayson (1979). That the axiom of choice
intuitionistically implies the law of excluded middle was proved in Goodman
and Myhill (1978), reformulating in purely logical terms the fundamental result
of Diaconescu (1975). The derivation of that law from the Schr¨oder–Bernstein
theorem was carried out in a category-theoretic setting by Banaschewski and
Br¨ummer (1986): the proof given here extends their result to intuitionistic set
theory. Banaschewski and Bhutani (1986) showed that the Stone representation
theorem implies the law of excluded middle within the context of so-called localic
toposes; the extension of their result to intuitionistic set theory, and the proof
given here, is due to Bell (1999).
It seems to have been Higgs (1973) who first extended to Heyting algebras
the theory of Boolean-valued models, but the systematic development of the
idea, and its use in providing models of intuitionistic set theory, is due mainly
to Grayson (1975, 1979). In particular, the observation that Zorn’s lemma holds
in Heyting-algebra-valued models was made by Grayson (1975).
Appendix
The concept of elementary topos was invented by Lawvere and
Tierney (Lawvere 1971, Tierney 1972) in the late 1960s: it has proved to be an
idea of immense fertility. Diaconescu’s theorem appears in Diaconescu (1975).
The idea of an H-set was introduced and developed by Fourman and Scott
(1979), where its connections with sheaf theory are explicitly worked out. H-sets
were independently invented and studied by Higgs (1973): there one finds, in
particular, the equivalence between Set(H) and SetH.

```

## PDF page 204 | printed page 184

```text
BIBLIOGRAPHY
Balbes, R. and Dwinger, P. (1974). Distributive Lattices. University of Missouri
Press, Columbia, Missouri.
Banaschewski, B. and Bhutani, L. (1986). Boolean algebras in a localic topos.
Math. Proc. Camb. Philos. Soc. 100 (1), 43–55.
Banaschewski, B. and Br¨ummer, G. (1986). Thoughts on the Cantor–Bernstein
theorem. Quaestiones Math. 9 (1–4), 1–27.
Bell, J. L. (1975). A characterization of complete Boolean algebras. J. London
Math. Soc. 12 (2), 86–88.
Bell, J. L. (1976). Uncountable Standard models of ZFC+V ̸= L. Set Theory and
Hierarchy Theory: A Memorial Tribute to A. Mostowski, Birutowice, Poland
1975. Lecture Notes in Mathematics, vol. 537, Springer, Berlin–Heidelberg–
New York.
Bell, J. L. (1976a). A note on generic ultrafilters. Z. Math. Logik 22, 307–310.
Bell, J. L. (1981). Isomorphism of structures in S-toposes. J. Symbolic Logic 46
(3), 449–459.
Bell, J. L. (1983). On the strength of the Sikorski extension theorem for Boolean
algebras. J. Symbolic Logic 48 (3), 841–846.
Bell, J. L. (1988). Toposes and Local Set Theories: An Introduction. Oxford
Logic Guides 14. Clarendon Press, Oxford.
Bell, J. L. (1997). Zorn’s lemma and complete Boolean algebras in intuitionistic
type theories. J. Symbolic Logic 62 (4), 1265–1279.
Bell, J. L. (1999). Boolean algebras and distributive lattices treated construct-
ively. Math. Logic Quart. 45, 135–143.
Bell,
J. L. and Machover,
M. (1977).
A Course in Mathematical Logic.
North-Holland, Amsterdam.
Cohen, P. J. (1963). The independence of the continuum hypothesis I. Proc. Nat.
Acad. Sci. USA 50, 1143–1148.
Cohen, P. J. (1964). The independence of the continuum hypothesis II. Proc.
Nat. Acad. Sci. USA 51, 105–110.
Cohen, P. J. (1966). Set Theory and the Continuum Hypothesis. Benjamin,
New York.
Davis, M. (1977). A relativity principle in quantum mechanics. Int. J. Theor.
Phys. 16, 867–874.
Devlin,
K. J. (1977).
Constructibility.
In J. Barwise,
ed.,
Handbook of
Mathematical Logic. North-Holland, Amsterdam.
Devlin, K. J. and Johnsbraten, H. (1974). The Souslin Problem. Lecture Notes
in Mathematics, vol. 405, Springer, Berlin–Heidelberg–New York.

```

## PDF page 205 | printed page 185

```text
BIBLIOGRAPHY
185
Diaconescu, R. (1975a). Axiom of choice and complementation. Proc. Amer.
Math. Soc. 51, 176–178.
Dickmann, M. (1975). Large Infinitary Languages. North-Holland, Amsterdam.
Drake, F. R. (1974). Set Theory: An Introduction to Large Cardinals. North-
Holland, Amsterdam.
Easton, W. B. (1970). Powers of regular cardinals. Ann. Math. Logic 1,
141–178.
Ellentuck, E. (1976). Categoricity regained. J. Symbolic Logic 41, 639–643.
Feferman, S. (1965). Some applications of the notions of forcing and generic sets.
Fund. Math. 56, 325–345.
Felgner, U. (1971). Models of ZF-set Theory. Lecture Notes in Mathematics,
vol. 223, Springer, Berlin–Heidelberg–New York.
Fitting, M. C. (1969). Intuitionistic Logic, Model Theory and Forcing. North-
Holland, Amsterdam.
Fourman, M. P. and Hyland, J. M. E. (1979). Sheaf models for analysis.
In Fourman Mulvey and Scott eds. (1979), pp. 280–302.
Fourman, M. P. and Scott, D. S. (1979). Sheaves and logic. In Fourman Mulvey
and Scott eds. (1979), pp. 302–401.
Fourman, M. P., Mulvey, C. J., and Scott, D. S. eds. (1979). Applications
of Sheaves.
Proc.
L.M.S. Durham Symposium 1977.
Lecture Notes in
Mathematics, vol. 753, Springer, Berlin–Heidelberg–New York.
Goldblatt, R. I. (1979). Topoi: The Categorical Analysis of Logic. North-Holland,
Amsterdam.
Goodman, N. and Myhill, J. (1978). Choice implies excluded middle. Z. Math.
Logik Grundlag. Math. 24 (5), 461.
Grayson, R. J. (1975). A sheaf approach to models of set theory. M.Sc. thesis,
Oxford University.
Grayson, R. J. (1978). Intuitionistic set theory. D. Phil. Thesis, Oxford
University.
Grayson, R. J. (1979). Heyting-valued models for intuitionistic set theory.
In Fourman Mulvey and Scott eds. (1979), pp. 402–414.
Grigorieff, S. (1975). Intermediate submodels and generic extensions in set
theory. Ann. Math. 101, 447–490.
Halmos, P. R. (1963). Lectures on Boolean Algebras. Van Nostrand, New York.
Halmos, P. R. (1965). Measure Theory. Van Nostrand, New York.
Higgs, D. (1973). A category approach to Boolean-valued set theory. (Unpub-
lished typescript, University of Waterloo.)
Jauch, J. M. (1968). Foundations of Quantum Mechanics. Addison-Wesley,
Reading, MA.
Jech, T. J. (1967). Non-provability of Souslin’s hypothesis. Comment. Math.
Univ. Carolinae 8, 291–305.
Jech, T. J. (1971). Lectures in Set Theory. Lecture Notes in Mathematics,
vol. 217, Springer, Berlin–Heidelberg–New York.
Jech, T. J. (1973). The Axiom of Choice. North-Holland, Amsterdam.

```

## PDF page 206 | printed page 186

```text
186
BIBLIOGRAPHY
Jech, T. J., ed. (1974). Axiomatic Set Theory. AMS Proceedings of Symosia
in Pure Mathematics, vol. XIII, Part II. American Mathematical Society,
Providence.
Johnstone, P. T. (1977). Topos Theory. Academic Press, London.
Johnstone,
P. T. (1982).
Stone Spaces.
Cambridge Studies in Advanced
Mathematics 3. Cambridge University Press, Cambridge.
Johnstone, P. T. (2002). Sketches of an Elephant: A Topos Theory Compendium,
vols. I and II. Oxford Logic Guides vols. 43 and 44, Clarendon Press, Oxford.
Kelley, J. L. (1955). General Topology. Van Nostrand, New York.
Kripke, S. (1967). An extension of a theorem of Gaifman-Hales-Solovay. Fund.
Math. 61, 29–32.
Kunen, K. (1980). Set Theory. North-Holland, Amsterdam.
Lambek, J. and Scott, P. J. (1986). Introduction to Higher-Order Categorical
Logic. Cambridge University Press, Cambridge.
Lawvere, F. W. (1971). Quantifiers and sheaves. In Actes du Congr`es Intern.
Des. Math. Nice 1970, tome I. Gauthier-Villars, Paris, pp. 329–334.
Levy, A. (1965). Definability in axiomatic set theory I. Proceedings of the 1964
International Congress on Logic, Methodology and Philosophy of Science.
North-Holland, Amsterdam.
Levy, A. and Solovay, R. M. (1967). Measurable cardinals and the continuum
hypothesis. Israel J. Math. 5, 234–238.
Mac Lane, S. (1971). Categories for the Working Mathematician. Springer-
Verlag, Berlin.
Mac Lane,
S. (1975).
Sets,
topoi,
and internal logic in categories.
In
H. E. Rose and J. C. Shepherdson, eds., Logic Colloquium 73, pp. 119–134.
North-Holland, Amsterdam.
Mac Lane, S. and Moerdijk, I. (1992). Sheaves in Geometry and Logic: A First
Introduction to Topos Theory. Springer-Verlag, Berlin.
Martin, D. A. and Solovay, R. M. (1967). Internal Cohen extensions. Ann. Math.
Logic 2, 143–178.
McLarty,
C. (1992).
Elementary Categories,
Elementary Toposes.
Oxford
University Press, Oxford.
Miller, E. W. (1943). A note on Souslin’s problem. Amer. J. Math. 65,
673–678.
Mitchell, W. (1972). Boolean topoi and the theory of sets. J. Pure Appl. Algebra
2, 261–274.
Osius, G. (1974a). Categorical Set Theory: a characterization of the category of
sets. J. Pure Appl. Algebra 4, 79–119.
Rasiowa, H. and Sikorski, R. (1963). The Mathematics of Metamathematics.
PWN, Warsaw.
Rosser, J. B. (1969). Simplified Independence Proofs: Boolean-Valued Models of
Set Theory. Academic Press, New York.
Rudin, M. E. (1977). Martin’s Axiom. In J. Barwise, ed., Handbook of
Mathematical Logic. North-Holland, Amsterdam.

```

## PDF page 207 | printed page 187

```text
BIBLIOGRAPHY
187
Scott, D. S. (1967). Boolean-Valued Models for Set Theory. Mimeographed notes
for the 1967 American Math. Soc. Symposium on axiomatic set theory.
Scott, D. S. (1968). Extending the topological interpretation to intuitionistic
analysis I. Compositio Math. 20, 194–210.
Scott, D. S. (1969). Boolean-valued models and non-standard analysis. Applic-
ations of Model Theory to Analysis, Algebra and Probability. Holt, Reinhart
and Winston, New York.
Scott, D. S. (1970). Extending the topological interpretation to intuitionistic
analysis II. In A. Kino, J. Myhill, and R. E. Vesley, eds., Intuitionism and
Proof Theory, pp. 235–256. North-Holland, Amsterdam.
Scott, D. S., ed. (1971). Axiomatic Set Theory. AMS Proceedings of Symo-
sia in Pure Mathematics, vol. XIII, Part I. American Mathematical Society,
Providence.
Shoenfield, J. R. (1971). Unramified forcing. In Scott, ed. (1971).
Sikorski, R. (1964). Boolean Algebras. Springer, Berlin–Heidelberg–New York.
Solovay, R. M. (1965). 2ℵ0 can be anything it ought to be. In J. W. Addison,
L. Henkin, and A. Tarski, eds., The Theory of Models. North-Holland,
Amsterdam.
Solovay, R. M. (1966). New proof of a theorem of Gaifman and Hales. Bull.
Amer. Math. Soc. 72, 282–284.
Solovay, R. M. (1970). A model of set theory in which every set of reals is
Lebesgue measurable. Ann. Math. 92, 1–56.
Solovay, R. M. and Tennenbaum, S. (1971). Iterated Cohen extensions and
Souslin’s problem. Ann. Math. 94, 201–245.
Takeuti, G. (1978). Two Applications of Logic to Mathematics. Princeton
University Press, Princeton.
Takeuti, G. and Zaring, W. M. (1973). Axiomatic Set Theory. Springer,
Berlin–Heidelberg–New York.
Tennenbaum, S. (1968). Souslin’s problem. Proc. Nat. Acad. Sci. USA 59, 60–63.
Tierney,
M.
(1972).
Sheaf
theory
and
the
continuum
hypothesis.
In
F. W. Lawvere, ed., Toposes, Algebraic Geometry and Logic. Springer Lecture
Notes in Math. 274, pp. 13–42.
Vopˇenka, P. (1965). The limits of sheaves and applications on constructions of
models. Bull. Acad. Polon. Sci. Ser. Sci. Math. Astron. Phys. 13, 189–192.
Vopˇenka, P. (1967). General theory of ∇-models. Comment. Math. Univ.
Carolinae 8, 145–170.
Vopˇenka, P. and Hajek, P. (1972). The Theory of Semisets. North-Holland,
Amsterdam.

```

## PDF page 208 | printed page 188

```text
INDEX OF SYMBOLS
A ∗B 147
AC 17, 159
a0 · u0 + a1 · u1 33
Aut(B) 71
B ⊗C 128
¯
B 155
Cκ(x, y) 68
C(x, y) 57
ccc 50
ccg 116
cf 67
CH 18
Comp(p, q) 55
Consis(T) 27
DEM 13
dom(f) 17
false 159
f[X] 16
f|X 16
Fun(f) 16
GJ 83
Gn 83
G∗105
G∗∗105
GCH 18
gx 71
¯h 76
˜h 76
HOD 76
(HODM)M[U] 108
i 91
iU 92
IZ 158
IZF 163
j 92
J(C) 135
κ+ 18
κ −cc 53
κλ 18
LDN 13
LEM 13
L 16
L 16
Lα 47
L(x) 16
L(B) 21
L(B)
M
88
L(Γ) 80
LS 108
L(B)
S
108
L 112
L∞ω 112
lim
→Bi 138
lim coi∈IBi 138
M 88
M(B) 88
M(B)/U 88
M[G] 104
M[U] 91
MA 127
MAκ 125
MAκ! 126
N(p) 57
(ODM)M[U] 108
Op 55
o(x) 121
O(X) 2
OD 76
HOD 76
ORD(M) 90
Ord(x) 16
Ω159
P (B)(u) 43
P(x) 16
PX 16
Px 16
π · b 71
RB 149
ran(f) 17
rank(x) 19
RO(P) 55
RO(X) 7
S1 90
S2 92
S3 94
SB 160
SH 120
stab 79
[PDF-GLYPH-U+0001]
i∈I ai · ui 33
t(M) 19
true 159
U 88
U+ 132
U∗93
V 16
[PDF-GLYPH-U+0002]V 100
Vα 19
V (B) 21
V (B)
α
21
V (H) 165
V (Γ) 78
V (Γ)
α
78
V (2) 20
V (2)
α
20
WLDN 14
WOϕ 74
ˆx 30
xU 88
xy 16
X + Y 171
χ(m) 172
Y X 173
ZF 17
ZFC 18
ZFM 111
0 1
0L 1
1 1
1L 1
2 7
|x| 18
⟨u, v⟩(B) 52
⟨x, y⟩16
[PDF-GLYPH-U+0001]·[PDF-GLYPH-U+0002]B 22
[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002] 88
[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]B 23
[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]H 165
[PDF-GLYPH-U+0001]σ[PDF-GLYPH-U+0002]Γ 80
{u, v}(B) 52
{u}(B) 52
{x ∈u : ϕ(x}(B) 76
∈16
∈U 89
∧1
[PDF-GLYPH-U+0003] 2
∨1
[PDF-GLYPH-U+0004] 2
∼U 88
⇒3
⇔3
∗3
|= 19
⊩58
⊩c 60
⊩Γ 81
⊪167
≤1
≤B⊗C 128
∼
= 112
∼
=C 112
∼
=Bool 112
∼
=∞ω 112
∼
=part 112
↠170
↣170
[PDF-GLYPH-U+0005]
i∈I Ai 173
[PDF-GLYPH-U+0006]
i∈I Ai 174
Set 169
Set→176
SetP 176
SetH 180
Set(H) 179
Shv(H) 177

```

## PDF page 209 | printed page 189

```text
INDEX
action by automorphisms 71
algebra of opens 5
two-element 7
of truth values 158, 179
Lindenbaum 14
quotient 10
Algebraic Completeness Theorem 15
almost everywhere 151
amenable 170
antichain 33
arrow 169
epic 170
monic 170
identity 169
atom 101
automorphism 10
Axiom, Extensionality 17
of infinity 17
Pairing 158
Power set 17
Regularity 17
Replacement 17
Separation 17
of Choice 17, 159
of Constructibility 18
B-extension 21, 88
B-formula 22
B-sentence 22
basis 56
bivalent 179
Boolean algebra 6
categorical 116
completion 50, 57
extension 21
isomorphic 112
operations 7
topos 178
-valued model of ZFC 37, 88
Boolean-valued Structure 28
bottom element 1
bounded 1
branch 120
canonical bijection 18
embedding 130
generic set 105
generic ultrafilter 97
homomorphism 10
map of M(B) onto M[U] 92
projection 140
cardinal 18
collapsing 109
Cartesian closed 175
category 169
of sets 169
characteristic function 20
map 158
Church’s scheme 16
class of all ordinals 16
classical logic 13
closure 155
cofinality 67
collapsing algebra 110
commutative diagram 92, 170
commutable 155
commute 154
compatible 55
complete 2
Boolean projection algebra 154
F- 95
finitely 175
homomorphism 9, 76
subalgebra 29
complement 5, 178
complemented 7
completely embedded 118
completion of a Boolean algebra 56, 138
composite 169
condition 55
continuum hypothesis 18
generalized 18
coproduct 171, 174
core 37
countable chain condition 50, 63
countably M-complete 101
completely generated 116
De Morgan’s law 13
decidable 159
decomposition 170
definable class 16

```

## PDF page 210 | printed page 190

```text
190
INDEX
definite 43
dense 55, 103
below an element 103
Diaconescu’s Theorem 178
direct limit 138
distributive 2
domain 16
Einstein–Podolsky–Rosen paradox 157
element (in category) 170
equalizer 172
equivalence 3, 175
extensional 181
field of sets 7
filter 8
of subgroups 79
prime 8
finite meet property 8
forces 58
Γ- 81
formula 22
functor 174
free 120
generating class 181
generic extension 97
group actions 72
of automorphisms 10
H-set 180
height 120
Heyting algebra 3
valid 14
algebra–valued structure 15
holds with probability 1, 24
homogeneous 73
homomorphism 9
ideal 8
image 170
implication 3
Induction principle for V (B) 21
injection 147
interpretation 19
intuitionistic forcing 167
logic 13
Zermelo set theory 158
invariant 73
involution 107
isomorphic 10
partially 112
isomorphism 10
partial 112
Iteration lemma 104
Iteration theorem 146
join 1
κ-chain condition 53
κ-complete 111
(κ, λ)-distributive 68
(L -) structure 15
language of set theory 16
infinitary 112
law of double negation 13
excluded middle 13
lattice 1
complete 2
of sets 1
limit completion 138
M-generic 89
ultrafilter generated by G 104
M-partition of unity in B 89
Martin’s axiom 127
at level κ 125
Maximum Principle 35
measure space 150
measurable cardinal 111
meet 1
Mixing Lemma 33
mixture 33
two-term 33
model of ZFC generated by U and M 98
obtained by adjoining U to M 98
Mostowski’s Collapsing Lemma 19
natural transformation 175
nonprincipal 111
normal filter 79
sequence 138
object 169
exponential 173
initial 170
power 173
terminal 170
truth value 172
Order Extension Principle 162
order topology 55
ordered pair in V (B) 52
ordinal 163
in M(B)/U 90
ordinal definable 76
hereditarily 76
orthomodular 153

```

## PDF page 211 | printed page 191

```text
INDEX
191
partition of unity 33, 89
power set 16
algebra 7
in V (B) 43
presheaf 177
product 171, 173
Product Lemma 104
projection 153
pseudocomplementation 3
pullback 171
Rasiowa–Sikorski Theorem 10
real numbers 149
reduced measure algebra 150
refined 55
associate 57
regular 8, 18
open 7
algebra 7
regularization 8
restricted formula 19
S-complete 10
S-generic 120
Schr¨oder–Bernstein Theorem 160
sentence 22
set of conditions 56
sheaf 177
σ-algebra 149
σ-field 150
σ-ideal 149
Sikorski extension theorem 148
simple 163
Souslin tree 121
Souslin’s Hypothesis 120
spectral family 154
stabilizer 79
standard 30
ordinal 45, 90
Stone representation theorem 11, 161
strong forcing 60
subalgebra 5, 7
subextensional 181
sublattice 1
subobject 172
classifier 172
subordinal 163
top element 1
topos 175
transitive 163, 175
collapse 19
∈-model 19
∈-structure 19
tree 120
trivial lattice 8
true 24
two-slit experiment 157
two-valued set 20
ultrafilter 8
ultrapower 78
universe of sets 16
of constructible sets 16
of B-valued sets 21
of H-valued sets 165
two-valued sets 20
valid 24
weak forcing 60
law of double negation 14
law of excluded middle 13
well-founded relations 18
Zermelo–Fraenkel set theory 17
intuitionistic 163
Zorn’s Lemma 16, 166
∞ω-theory 112
∞ω-equivalent 112

```
