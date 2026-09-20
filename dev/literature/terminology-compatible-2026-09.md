# The compatibility collision, evidence for an owner ruling

Date: 2026-09-12. Status: BLOCKED ON AN OWNER RULING. Blocks all prose in K2, K3,
K4 and K5; blocks no code, and none of those packages has waited on it. This note
carries the evidence so the ruling is a decision rather than an investigation.
It proposes options and does not choose; the project rule is that parallel
authors may not resolve a terminology collision.

## The collision

`dev/glossary.toml` carries, owner-ruled 2026-08-03:

```
en = "coherence"   zh = "相容"   ja = "整合"
notes = "the restriction-compatibility of the level orders"
```

K2 introduced the structural forcing vocabulary, in which two conditions are
COMPATIBLE when they have a common refinement. The standard Chinese rendering of
that notion is 相容. So the same Chinese word would carry two technical senses in
one book.

## What makes this awkward rather than routine

The ruled entry is ITSELF a compatibility notion. Its own note says so: the
restriction-compatibility of the level orders. So this is not two unrelated terms
colliding on one word; it is one concept appearing in two places, and the
question is whether the book should let them share a word or should distinguish
them.

That cuts both ways and the ruling turns on which the owner prefers.

If they share the word, a reader who meets 相容 in the forcing chapters and again
in the level-order chapters is being told, correctly, that these are instances of
one idea. The cost is that the two have different formal definitions and a reader
tracking a definition backwards will find two.

If they are distinguished, each definition has its own name and the backwards
search is unambiguous. The cost is that the book hides a real commonality, and
whichever of the two loses 相容 acquires a second-choice word.

## What each side would cost in the tree

The ruled entry is consumed by the level-order and stage-order material, which is
K0-era and already written. Changing it means revisiting settled prose.

Forcing compatibility is consumed by K2's poset layer and everything above it,
which is written in Agda and has NO Chinese prose yet, because the terminology
track has been blocked from the start. Changing it costs nothing today and grows
more expensive with every package that writes prose.

That asymmetry is the one practical fact the ruling should weigh: the cheaper
move today is to give forcing compatibility a different word, and the cheapest
moment to decide is before K2's prose is written.

## The options, stated so a ruling can name one

1. Forcing compatibility takes a different Chinese word and 相容 stays with the
   2026-08-03 entry. A candidate is 可兼容 or a qualified form such as 条件相容
   that keeps the shared root while marking which sense is meant.
2. The 2026-08-03 entry is revisited and yields 相容 to forcing compatibility,
   taking another word for the restriction-compatibility of level orders.
3. Both keep 相容 and the glossary records that the book uses one word for two
   formally distinct instances of one idea, with a cross reference at each.

## What is not being asked

Nothing here questions the 2026-08-03 ruling on its merits. The entry was ruled
with a stated reason and that reason still holds. What is new is only that a
later package introduced a second use of the same idea, which was not visible
when the entry was ruled.

## Method note

No literature search was run for this note, and that is deliberate rather than an
omission: the project rule is to search the literature before INTRODUCING or
REVISING terminology, and a collision between two already-ruled or
about-to-be-ruled senses is a question about the book's own conventions rather
than about what the literature calls either notion. A literature check on the
standard rendering of forcing compatibility should follow whichever option the
ruling names, and belongs with the glossary batch that implements it.

## Until then

K2, K3, K4 and K5 have proceeded with English-only source prose, which is what
the current phase permits. No Chinese or Japanese rendering of either sense has
been written by any agent, and no parallel author has invented a competing
translation. That is the state the rule exists to protect and it has held.
