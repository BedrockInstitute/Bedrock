# Review of `internal-nonempty`

The obligation is a hole. This file is the obstruction, for the branch
`no-go-stated`.

## THE STATEMENT

```
internal-nonempty :
  ∥ Σ[ δ ∈ Mem (Lset β) ]
      ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁ ∥₁
```

It is `Probe425.agda:85-92`, with `open SiteBound κ`
(`src/L/Cardinal.lagda.md:163-172`). Generic in `κ` with `oκ` as a
module parameter. No cardinal, no band, no numeral. Agda reports
`UnsolvedInteractionMetas` at `Probe425.agda:92`
(`runs/final-hole.out`, exit 42, 1.93 s, caliber
`GHCRTS="-A64m -I0 -M8g"`). The hole is `graph-code`, the `F`
conjunct. The `δ := κ` conjunct is green (`δκ`, `Probe425.agda:71-72`).

## D-10

FALSE at this witness, at the intended generality. See
`lj-1.425-report.md` section D-10.

`β` is `stageBound (fst κ) (snd κ) .fst`
(`src/L/Cardinal.lagda.md:166`), i.e. `bound2 ω (stage κ)`
(`src/L/Choice/Stage.lagda.md:366-368`). That ordinal contains `ω` and
`stage κ`. It does not contain `sucV (stage κ)`.

The identity graph's members are ordered pairs of members of `κ`.
Those pairs sit two stages up: `pr∈Lset-suc`
(`src/L/Axioms/Basic.lagda.md:596-597`). Carve's bound is a sealed
`boundingOrd` over that pair family (`src/L/InjChain.lagda.md:75-93`).
The tree states no comparison between that bound and `β`.

The site bound's one downward bridge is `bound-below₂`
(`src/L/Choice/Stage.lagda.md:370-373`): members of members of `κ`. A
pair is not a member of a member.

So `κ ∈ Lset β` holds and `F ∈ Lset β` fails for this graph.

## WHICH BOUND FAILS TO CONTAIN THE OTHER

The site bound `β` fails to contain the graph's bound. The elaborator
does not compare the two ordinals, because no lemma does. What it
reports is the missing `F` conjunct:

```
UnsolvedInteractionMetas
  agents/tasks/LJ-1-425/Probe425.agda:92.18-22
```

Cite: `runs/final-hole.out`. W3 measured the same gap as a premise:
`graph-in-site-bound` typechecks only from
`⟨ stage (fst G) (snd G) ∈ˢ β ⟩` (`Probe425.agda:49-54`). That
premise is not delivered.

## WHAT WAS NOT DONE

InclGraph was not applied. D-10 already stops the membership. Carve's
private `Small` instance (`src/L/InjChain.lagda.md:552-553`) is the
8g heap warning; this task does not need `Small`. The four conjuncts
stay where the chapter left them (`src/L/InjChain.lagda.md:518-547`).

No axiom, no postulate, no module parameter that asserts
`⟨ fst G ∈ˢ Lset β ⟩`. The obligation stays a hole.

## CORRECTED TARGET

Quantify over a stage that contains `sucV (sucV (sucV (stage κ)))` as
well as `β`, so `pr∈Lset-suc` and one `𝒟ₒ` step both land inside it.
Re-carving the identity graph inside the present `Lset β` does not
repair the witness: the pairs themselves are not members of
`Lset (stage κ)`.

## C-42

COUNT of `src/` sites that ask for a graph or an `InjCode` witness as
`Mem (Lset β)` with `β` from `stageBound`: **2**. Both sit in
`src/L/Cardinal.lagda.md`. The table is in `lj-1.425-report.md`
section C-42. No other `src/` file instantiates `Selected`.
