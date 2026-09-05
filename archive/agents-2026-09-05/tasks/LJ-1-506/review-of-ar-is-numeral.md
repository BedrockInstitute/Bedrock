# review-of-ar-is-numeral: the statement the brief wrote is FALSE, and the repair is one equation

**THIS FILE CARRIES THE STOP HALF OF `[LJ-1.506]`.** The term is built and the
probe is green. Read `agents/tasks/LJ-1-506/lj-1.506-report.md` for the whole
return. **This file exists because a green probe must not be read as "eleven
field positions are now paid". THEY ARE NOT.**

## THE STOP

**The brief's type, with `C` left a bare `S`, is not a theorem.**

    ar-is-numeral :
        (k : ℕ) (c ar a b : S)
      → ⟨ fst c ∈ fst C ⟩
      → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
      → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁

**REFUTED, MACHINE-CHECKED**, at `agents/tasks/LJ-1-506/Probe506.agda:143-150`,
exit 0. The counterexample is `sucʟ` of a pair whose first component is `ωʟ`
(`:122-126`). `ω` is not a numeral, by `#∈ω` (`src/L/Ordinal.lagda.md:248`) and
`∈-irrefl` (`src/V/Hierarchy.lagda.md:155`).

**I did not weaken the truncation and I did not add a numeral hypothesis.** The
brief forbade both and I obeyed both. The one entry I added names the set:
`fst C ≡ fst (AllCodes A)`.

## WHY THE BRIEF COULD NOT HAVE ASKED FOR LESS

**D-10 says price the truth of the target before pricing its proof, and the
target was false at the generality the brief chose.** The brief's own premise 10
is right that the code set sits at slot two of the record's environment
(`src/L/Condensation/TwelveAgree.lagda.md:162`). **A slot is the problem.**
`TFacts`'s `γ' : S ^ (11 + n)` (`:129-131`) is unconstrained, so slot two ranges
over every set of `L`, and almost none of them are code sets.

**AND `KValue` IS NOT THE FRAME THE BRIEF THOUGHT IT WAS.** `KValue` supplies a
`KFacts` value (`src/L/Condensation.lagda.md:7411`), and `KFacts`
(`:6079-6115`) **has no `codesK` field and no code-set slot**. Its `Kenv`
(`:7389-7392`) holds the carrier, the bound and twelve arity tags. **The code
set is absent at that frame, not merely unconstrained.**

## WHAT MAKES IT TRUE

`AllCodes A` (`src/L/Coding/CodeSet.lagda.md:440`) is the constructed code set,
and its first conjunct `arityNumAtL` (`:185-187`) was written to pay this exact
debt (`:24-27`). With the set named, the term is `PT.map` and `pr-inj`:

- `codeset-numeral`, `Probe506.agda:56-59`. **W3, and no `subst` in it.**
- `ar-is-numeral`, `Probe506.agda:79-86`. Eight lines.
- `AtSlot`, `Probe506.agda:160-173`. The `lookup C γ'` form a frame would apply.

**THE EQUATION IS CHEAPER THAN THE ONE `[LJ-1.86]` STOPPED ON.** That task needed
`AllCodes A` inside `Lset lam`, and `lam` is a module parameter at every frame
(`archive/dev/LJ-dispatch-index.md:160`). **`AtSlot` names `A`, `C` and `γ'`
only.** It never mentions `lam`, `Lset` or `K`.

## WHAT THE MATHEMATICIAN MUST DECIDE, AND I MUST NOT

**Adding the equation changes `codesK`'s TYPE at 25 sites**, because the fourth
component stops being a field and becomes a derivation. That is a redesign of a
record with 59 field positions and no value in the tree. **AD3 gives that
judgement to the mathematician.** I priced it and I stopped there.

**THE SWEEP IS WIDER THAN THE TERM (C-42).** 23 further declarations state
`valK` or `valK-un` over the same bare code slot. **I did not refute those and I
did not price their cure.** The counts and every `file:line` are in the report
under `## THE C-42 SWEEP`.

## WHAT THIS DOES NOT SAY

**It does not say the tree cannot prove the truncation. It can.**
`[LJ-1.83-A]` recorded this debt as OWED in July
(`archive/dev/LJ-dispatch-index.md:157`), and `[LJ-1.85]` already found the same
cure for `witK` (`:159`). **This task proves the cure works for the arity
component and measures that the component needs no stage.**
