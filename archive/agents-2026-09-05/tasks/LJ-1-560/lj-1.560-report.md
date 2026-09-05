# [LJ-1.560] report: bound one unbounded search to a stage

**GO. THE OBLIGATION IS INHABITED, AND IT IS AN INSTANTIATION.**
`agents/tasks/LJ-1-560/Probe560.agda:165-176`, exit 0.

**THE ESTIMATE WAS FAR TOO HIGH AND THE BRIEF SAID TO SAY SO.** The brief
estimated about 170 lines with the obligation at about 45. The obligation is
**12 lines of type and 5 lines of term**
(`agents/tasks/LJ-1-560/Probe560.agda:165-176`), and the term is three library
names and one constructor. The brief's own instruction applies: "If the chapter
already has it, the estimate above is far too high and you should say so and
finish early."

**NOTHING LANDS IN `src/`. NO HOLE, NO POSTULATE, NO COMMIT, NO PUSH.**

## WHAT REFLECT ALREADY HAS

**IT HAS A REFLECTION PRINCIPLE. IT IS NOT ONLY THE `Ladder` CONSTRUCTION.**
The chapter's own title is `src/L/Reflect.lagda.md:1`, "Reflecting an
existential into a stage", and the D-10 the brief ordered is answered by reading
the chapter rather than the summary.

| At `file:line` | What it is |
|---|---|
| `src/L/Reflect.lagda.md:253-254` | `ClosedFor β ψ`: every environment drawn from `β` that satisfies `∃̇ ψ` anywhere in L has a witness in `Lset β`. **This is the obligation's sentence, already named.** |
| `src/L/Reflect.lagda.md:411` | `Ladder.reflect`, the principle proved of any ladder that answers |
| `src/L/Reflect.lagda.md:442` | `module Single`, the ladder for one matrix |
| `src/L/Reflect.lagda.md:492` | `Single.closed : ClosedFor βω ψ`. **The obligation, discharged, in `src/`.** |
| `src/L/Reflect.lagda.md:495` | `Single.reflect`, the same as an EQUALITY of truth values |
| `src/L/Reflect.lagda.md:164-165` | `Wit ψ ρ σ`, the search cut down to `Lset σ` |
| `src/L/Reflect.lagda.md:183`, `:210` | `pickStage`/`pickWitness`, the POINTWISE answer, which needs no ladder |
| `src/L/Reflect.lagda.md:256`, `:271` | `Ladder`, `top-ord`, which is all `[LJ-1.544]` used |

**AND THE SUCCESSOR CHAPTER IS STRICTLY STRONGER.** `src/L/ReflectFo.lagda.md:525`,
`mkReflect`, takes **any formula of any complexity** plus **any ordinal the
caller needs inside the stage**, and returns a stage where the formula agrees
with its relativization. `src/FOL/Manipulation/Relativize.lagda.md:72`,
`Δ₀-relativize`, grades that relativization **Δ₀ with no hypothesis at all**.

**THAT CHAPTER IS ALREADY SPENT IN `src/`.** `src/L/Axioms/Full.lagda.md:144`,
`hasSeparationL`, is separation in L **at an arbitrary formula**, and its proof
at `src/L/Axioms/Full.lagda.md:151` is one `mkReflect` call.

**THE DIFFERENCE BETWEEN THE TWO, AND IT IS THE ONLY REASON TO PREFER `Single`:**

| | `Single.reflect` (`:495`) | `mkReflect` (`:525`) |
|---|---|---|
| Formula | one matrix under one `∃̇` | any formula, any complexity |
| Matrix afterwards | **untouched** | relativized |
| Stage above a prescribed ordinal | **no** | **yes**, `⟨ δ ∈ β ⟩` |

The obligation uses `Single`, because the obligation's sentence names `Lset β`
holding a witness **of the matrix the caller wrote**, and relativizing the matrix
would change that sentence. If a consumer needs the stage above an ordinal it
already holds, `Single` does not give it and `mkReflect` does.

## WHICH SIDE OF THE BOUNDARY

**THE TERM BOUNDS THE SEARCH IN THE OBJECT LANGUAGE, AND NOTHING REMAINS BEFORE
`AtStage` WOULD ACCEPT IT.** `Wit ψ ρ β`, which reads as a meta-level search cut
down to `Lset β`, **is** the object-language bounded existential
`∃̇∈ (con (LsetS β oβ)) ψ` read by the world's inner satisfaction: the two are
the same `Ω` by `refl`, at every stage and every formula
(`agents/tasks/LJ-1-560/Probe560.agda:130-133`, checked, exit 0).

So the obligation's second component
(`agents/tasks/LJ-1-560/Probe560.agda:173`) is an equality between two
satisfactions of two `Formula S k`, the left with an unbounded `∃̇` and the right
with a bounded `∃̇∈`, and `δ-∃∈` (`src/FOL/LevyHierarchy.lagda.md:57`) grades the
right Δ₀ as soon as the matrix is. **The boundary that stopped `[LJ-1.533]`,
`[LJ-1.549]`, `[LJ-1.552]` and `[LJ-1.554]` is not present at a stage**, and the
reason is deliberate design recorded upstream: `LsetS` keeps its first component
reducing so that "lies in the bound" and "lies in the stage" are the same
statement (`src/L/ReflectFo.lagda.md:88-96`).

## THE OBLIGATION

`agents/tasks/LJ-1-560/Probe560.agda:165-176`.

```
search-bounds :
  {k : ℕ} (ψ : Formula S (suc k))
  → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
      ( ((ρ : S ^ k) → Below β ρ → ⟨ ρ ⊨ (∃̇ ψ) ⟩ → ⟨ Wit ψ ρ β ⟩)
      × ((ρ : S ^ k) → Below β ρ → (ρ ⊨ (∃̇ ψ)) ≡ (ρ ⊨ boundAt ψ β oβ))
      × (Δ₀ ψ → Δ₀ (boundAt ψ β oβ)) )
```

**THE PREDICATE'S FORM, AS GENERALLY AS IT IS TRUE.** An arbitrary
`Formula S (suc k)`: one witness variable, `k` parameters, **no Levy grade, no
bound on the quantifiers already inside it, no hypothesis on the parameters
beyond membership of the stage**. "Satisfied somewhere in L" is `ρ ⊨ ∃̇ ψ`, read
by `_⊨ᵐ_`, which is the same inner satisfaction `defSet` reads
(`src/L/Definability.lagda.md:106-107`, `smallSat` reading `⊨ᵐ-small`, which
`defSet` at `:108-109` is defined over). The conclusion is truncated, which the brief
permits.

The term is `Single.βω ψ`, `Single.L.top-ord ψ`, `Single.closed ψ`,
`Single.reflect ψ`, `δ-∃∈`. That is the whole of it.

**THE STAGE IS LOAD-BEARING, AND THAT IS MEASURED, NOT ASSERTED.** The red
control `agents/tasks/LJ-1-560/runs/Red.agda` asserts the first conjunct at an
**arbitrary** stage. It FAILS, exit 42, `runs/red-1.out`, `UnequalTerms`.

## WHAT THE TWO BLOCKED LEGS GET

**THE CONDENSATION LEG'S NO-GO IS TRUE OF `AtStage` AND `AtStage` IS NOT THE
ONLY DOOR.** `[LJ-1.536]` is correct that `AtStage` wants Δ₀
(`src/L/Axioms/Separation.lagda.md:150`, `:163`) and it wants `BoundedFo` as
well. Two wrappers stand in front of it in `src/` today and each drops a
hypothesis. Both are re-ascribed in the probe, TYPE ONLY, and both typecheck:

1. `mkBoundedFo` (`src/L/Axioms/Separation.lagda.md:449`) produces the bounding
   stage for **any** formula by recursion. `BoundedFo` is never a cost.
   Probe `:208-210`.
2. `separateΔ₀` (`src/L/Axioms/Separation.lagda.md:481`) therefore needs the Δ₀
   witness **and nothing else**: no stage, no `BoundedFo`, no `𝒟ₒ-intro` by hand.
   Probe `:215-217`.
3. `hasSeparationL` (`src/L/Axioms/Full.lagda.md:144`) drops the Δ₀ hypothesis
   too, by reflecting the formula first. Probe `:223-225`.

**So the route into a stage that `[LJ-1.536]` measured as closed is open one
level up.** The premise the brief carries, that `𝒟ₒ-intro` is the one route into
a stage, is true of the primitive; it is not true of what a consumer must call.

**THE GCH LEG'S NAMED OBSTRUCTION IS EXACTLY WHAT SECTION 3 REMOVES.**
`[LJ-1.557]` measured that the uniform assignment needs a formula describing
`leastOf` at `w` over the code predicate, "which is a quantifier over the whole
L-carrier and not over a stage". `search-bounds` trades precisely one such
quantifier for a stage: `σ-∃` (`src/FOL/LevyHierarchy.lagda.md:75`) is the
constructor removed, and the trade is an **equality** of truth values, not an
implication (probe `:191-195`).

**WHAT IT DOES NOT DELIVER, AND THE MATHEMATICIAN SHOULD PRICE THIS BEFORE THE
NEXT BRIEF.** `ClosedFor` is **not** inherited by a larger stage: enlarging the
stage brings more environments that then want answering
(`src/L/ReflectFo.lagda.md:19`, "inherited by larger stages: enlarging the
stage admits more environments to", and `src/L/ReflectFo.lagda.md:498` says the
same of `mkReflect`'s certificate). So two stages cannot be merged into one
that carries both certificates, and a consumer that needs one stage to answer for
two different formulas must build the joint ladder, which is what
`src/L/ReflectFo.lagda.md:148` does: `Answers (∃̇ φ) σ oσ τ` pays the
single-matrix step for `φ` inside the joint step. **That is the shape to reach
for, and it is built.**

## THE PRICE

| Item | Number | Evidence |
|---|---|---|
| Probe, total lines | 225 | `agents/tasks/LJ-1-560/Probe560.agda` |
| The obligation itself | 12 type + 5 term | `Probe560.agda:165-176` |
| W3 slice, total lines | 81 | `agents/tasks/LJ-1-560/runs/W3.agda` |
| W3, typechecked ALONE, three runs | 1.05 s / 0.95 s / 0.97 s, exit 0 | `runs/w3-1.out` to `w3-3.out` |
| Whole probe, three runs | 1.65 s (exit 42) / 0.91 s / 0.91 s | `runs/final-1.out` to `final-3.out` |
| Red control | exit 42, as required | `runs/red-1.out` |

`final-1.out` is exit 42 and it is recorded rather than discarded: one error,
`UnequalTerms` at `Probe560.agda:215`, from instantiating `ModelL` through
`L.Model` (which carries `lem` as a parameter) instead of
`FOL.ZFModel 𝒮ʟ` directly, the way `src/L/Axioms/Full.lagda.md:68-69` does.
That is the only thing that failed in this task.

**The times are measured with the `src/` interfaces already built.** They are
not a cold-tree figure and must not be quoted as one.

**RATIO BAR.** Not applicable. The write scope holds no `.lagda.md` master, so
the in-fence line count is 0 and the bar cannot fire, exactly as the role block
states.

**CALIBER.** The program set `GHCRTS="-A64m -I0 -M8g"` on this pane; the value is
recorded at the head of `runs/w3-1.out`. I did not set it. One Agda process at a
time. **No heap wall.**

## GATES RUN

All exit 0, run from the worktree: `check-probes.py --check`,
`lint-agda.py --check`, `lint-prose.py --check`, `weave-i18n.py --check`,
`check-rule-ids.py`, `check-fences.py --check`.

**ONE ENVIRONMENT DEFECT, REPORTED AND NOT WORKED AROUND SILENTLY.** This
worktree has **no `.venv`**, so every `make` gate target fails with
`make: .venv/bin/python: No such file or directory`. I ran the gate scripts with
the main checkout's interpreter, `/Users/alsg/Agentic/Bedrock/.venv/bin/python`,
against this worktree's files, which is read-only against the other checkout. I
created nothing. **`make check` itself was NOT run and cannot be run here as the
worktree stands.**

## WHAT I WOULD ASK THE MATHEMATICIAN NEXT

1. **Does the consumer need the stage above an ordinal it already holds?** If
   yes, `Single` is the wrong tool and `mkReflect` is the right one, at the price
   of the relativized matrix. If no, section 3 is finished work.
2. **Does the consumer need one stage answering for two formulas?** If yes, the
   joint ladder of `src/L/ReflectFo.lagda.md` is the tool and neither
   certificate merges.
3. **`[LJ-1.561]` is measuring whether five stopped sites are one wall.** Two of
   them, `[LJ-1.536]` and `[LJ-1.557]`, stop at obstructions this task measures
   as already cured in `src/`. That is evidence for "one wall", and evidence that
   the wall is a **reading** of the tree and not a gap in it.

## ARCHIVE USED

- `archive/dev/JOURNAL-archived.md`. **READ AND USED.** At
  `archive/dev/JOURNAL-archived.md:408` the line reads
  "reflection trick makes every stage-carving Δ₀ after reflection, so the".
  This is the same finding as this task's, recorded before the archive was
  written, and it is why the report states the cure as existing rather than new.
- `archive/dev/LJ-dispatch-index.md`. **NOT USED, DECLINED.** Its one
  "reflection" hit is `LJ-1.269`, about Agda's own metaprogramming reflection,
  a different sense of the word entirely. Nothing about set-theoretic reflection.
- `archive/dev/JOURNAL.md`. **NOT USED, DECLINED.** Its three "reflection" hits
  are all the Agda metaprogramming sense as well (`:1160`, `:1180`, `:1183`).
- `dev/ARCHIVE.md`. **NOT USED, DECLINED.** Zero hits for "reflect". No retired
  module bears on this obligation, and this task retires nothing.
- `archive/dev/ORCHESTRATION.md`. **NOT USED, DECLINED.** Zero hits for
  "reflect"; it is the archived process document and carries no mathematics.

## LITERATURE USED

- `dev/literature/devlin-II5.md`. **READ AND USED.** At
  `dev/literature/devlin-II5.md:191` the line reads
  "reflects it down, so the witness z lies in X (`dev2.txt:1173-1183`)."
  That is the classical statement of exactly this obligation's shape: a Σ₁
  statement reflected down so that the witness lands inside the smaller carrier.
  It is what told me the obligation's predicate should be an arbitrary matrix
  under one existential and not a special form.
- `dev/literature/digest.md`. **NOT USED, DECLINED.** Zero hits for "reflect".
- `dev/literature/truncation-and-selection.md`. **NOT USED, DECLINED.** Zero
  hits for "reflect". The obligation's conclusion is truncated, but it is
  truncated because `Wit` already is, and no selection principle is used or
  needed anywhere in this task.
- `dev/literature/geology.md`. **NOT USED, DECLINED.** Its two "reflect" hits
  are about set-theoretic geology, not about reflecting a formula into a stage.
- `dev/literature/terms-2026-08.md`. **NOT USED, DECLINED.** Zero hits for
  "reflect". It is a terminology file and this task proposes no term.
