# [LJ-1.590] report: StageOfCode, row 2's reflection step

**GO. THE OBLIGATION IS INHABITED.** `agents/tasks/LJ-1-590/Probe590.agda:179-182`,
exit 0 (`agents/tasks/LJ-1-590/runs/p-final.out`).

**IT IS AN INSTANTIATION, AND THE BRIEF SAID TO SAY SO AND FINISH EARLY.** The
brief estimated about 150 lines with the obligation at about 35. The obligation
is **18 lines** (`Probe590.agda:83-87` and `:165-182`), and every one of them is
a projection, a repack or a library name. Nothing is postulated. No hole. Nothing
lands in `src/`.

**BUT THE INSTANTIATION IS NOT THE ONE THE BRIEF NAMED.** See the next section.

## DID THE REFLECTION STEP APPLY

**NO.** `[LJ-1.560]`'s obligation `search-bounds`
(`agents/tasks/LJ-1-560/Probe560.agda:165-176`) does not apply at `StageOfCode`'s
frame. It is re-ascribed here as a type, `Probe590.agda:66-73`, and it typechecks,
so the comparison below is between two types that both exist and not between one
type and a description.

**THREE DIFFERENCES, EACH AT `file:line`, AND THE BRIEF PREDICTED NONE OF THEM.**
The brief expected "a reflection step that bounds a search over the L-carrier is
not automatically one that bounds a CODE". **That distinction is not the one
measured.** All three differences are about the ARGUMENT `search-bounds` takes.

| # | The difference | At |
|---|---|---|
| 1 | Its stage is a function of the FORMULA and of nothing else: `Single.βω ψ`. `StageOfCode`'s stage must be a function of `a` and `b`. Parameters ride in `ρ`, and `β` is chosen before `ρ` is seen. | `Probe560.agda:172`, `Probe583.agda:259-262` |
| 2 | Because the stage did not read the parameters, the caller must pay `Below β ρ`. `StageOfCode` gives no such hypothesis and cannot: `a` and `b` are arbitrary L-sets. | `src/L/Reflect.lagda.md:253` |
| 3 | Its conclusion is about an OBJECT-LANGUAGE formula. `InjCode F a b` is a META-LEVEL hProp. Reaching `search-bounds` at all first costs an internalization of `InjCode` as a `Formula S 3` plus soundness and completeness for it. | `src/L/Cardinal.lagda.md:223`, price written as a type at `Probe590.agda:134-140` and **NOT inhabited** |

Difference 1 is the same shape `[LJ-1.583]` already measured when it refused
`SiteBound`: "the bound the code needs is a function of a AND b, and the bound
`CodeSelect` offers is a function of a alone"
(`agents/tasks/LJ-1-583/Probe583.agda:218-220`). **The reflection ladder repeats
that error and does not repair it.** `mkReflect` (`src/L/ReflectFo.lagda.md:525`)
is the tree's repair for difference 2, and it takes ONE prescribed ordinal, not
two arbitrary L-sets.

**WHAT I HAD TO CHANGE, AND IT IS THE FINDING.** I went one layer BELOW the
reflection chapter. `L.Reflect` does not own its descent: it imports it
(`src/L/Reflect.lagda.md:54`, `open import L.Stage {ℓ} lem using ( LeastOrd;
leastOrd )`) and spends it pointwise at `src/L/Reflect.lagda.md:176`,
`pick ψ ρ sat = leastOrd (Wit ψ ρ) (witnessed ψ ρ sat)`.

**`L.Stage.leastOrd` (`src/L/Stage.lagda.md:149-153`) IS GENERIC IN THE
PREDICATE**, and it is the whole of this task:

```agda
leastOrd : ∥ (Σ[ α ∈ S ] (IsOrd α × ⟨ P α ⟩)) ∥₁ → LeastOrd
```

`StageOfCode` is that at one predicate. So the honest headline is: **the
reflection chapter's LADDER does not transfer, and its DESCENT was never the
reflection chapter's own.**

## WHAT ROW 2 NOW COSTS

**ONE ITEM.**

| item | before this task | after this task |
|---|---|---|
| `StageOfCode` | OPEN (`Probe583.agda:259-262`) | **PAID**, `Probe590.agda:179-182` |
| `SquareCoded` | OPEN (`Probe583.agda:195-196`) | **STILL OPEN. Untouched here.** |

`SquareCoded` is `[LJ-1.591]`'s question. AD12 gives this brief one obligation and
this file does not touch it. `Probe590.agda:215-220` says so in the file, so no
reader may take a coded factor from here.

**DO NOT READ MORE THAN THIS INTO IT.** Row 2's parent is `SetChoice`, defined at
`src/Base/Choice.lagda.md:55`. Nothing in this task speaks to that. What is
delivered is one term of one named type, plus the two compositions in the next
section, and nothing else.

## WHY IT WORKS, IN ONE SENTENCE

`[LJ-1.583]` named the gap correctly and then drew the wrong bound from it: "The
Σ is not a proposition, so the β cannot leave the truncation"
(`Probe583.agda:266-267`). **That sentence is true of an ARBITRARY β and false of
the LEAST one.** `BoundedCodeAt` is a truncation and so a proposition. `IsOrd` is
a proposition (`src/L/Constructible.lagda.md:144`). So the payload is a
proposition, the least ordinal carrying a propositional property is unique by
trichotomy (`src/L/Stage.lagda.md:94-107`), and the truncation lifts. The
excluded middle spent is the module's own hypothesis and is the one `leastOrd`
already spends at `src/L/Stage.lagda.md:137`. **No choice principle is added.**

## WHAT THE OBLIGATION BUYS

Both are compositions of terms that typecheck. Neither is a new argument.

- **THE TRUNCATION ESCAPE FOR CODES.** `InjL a b` is a truncation
  (`src/L/GCH.lagda.md:37-38`). Out of it, a code AS DATA:
  `bare-code-of : (a b : S) → InjL a b → Σ[ F ∈ S ] InjCode F a b`,
  `Probe590.agda:197-203`.
- **AND THE SAME READ AS AN INJECTION.**
  `bare-inj-of : (a b : S) → InjL a b → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫`,
  `Probe590.agda:207-213`.

Both use `[LJ-1.583]`'s `bare-code` (`Probe583.agda:251-252`) and `bare-inj`
(`Probe583.agda:254-255`) at the stage this task supplies. `[LJ-1.583]` had them
and could not reach them, because it had no β outside the truncation.

## W3, THE WIDEST UNMEASURED TERM

The brief named it: "`[LJ-1.560]`'s search-bounds, at `StageOfCode`'s frame, TYPE
ONLY", about 12 lines, under 2 minutes.

**WRITTEN FIRST AND TYPECHECKED ALONE**, at
`agents/tasks/LJ-1-590/runs/W3.agda`, exit 0, `runs/w3-1.out`, 0.95 seconds. It
carries three types: the re-ascription the brief asked for
(`runs/W3.agda:47-54`), the shape `StageOfCode` actually asks for
(`runs/W3.agda:58-61`), and the tree's device that has that shape
(`runs/W3.agda:64-71`).

**THE MEASURED NUMBER: 71 lines, 0.95 seconds.** The estimate said 12 lines and
under 2 minutes. The extra lines are the second and third types, which the brief
did not ask for and which are what settled the task. **W3 answered GO in under a
minute and the rest of the task followed from it.**

## WHAT RESISTED

**NOTHING RESISTED IN THE MATHEMATICS.** Two mechanical failures only, both
recorded because the next brief should not price them again:

1. `⟪_⟫` and `_↪_` were not imported (`runs/p-1.out`, exit 42, one scope error).
2. `stage-shape`'s result nests one Σ deeper than `StageOfCode` accepts, because
   `leastOrd` returns `IsOrd α` beside `⟨ P α ⟩` and `CodeAt` carries its own
   `IsOrd α` inside. Fixed by projecting `sh .snd .snd .fst` rather than
   `sh .snd .fst` (`Probe590.agda:180`). `runs/p-2.out`, exit 42, one
   `UnequalTerms`.

Three runs to green, 9.44 + 1.53 + 1.75 seconds. No heap wall. No unsolved meta.

## WHAT I COULD NOT CLOSE

Nothing that the brief asked for. `ViaSearchBounds` (`Probe590.agda:134-140`) is
**deliberately not inhabited**: it is the price of the route this task rejected,
written as a type so that a later brief can price it instead of guessing at it.
If a future task really needs `InjCode` as an object-language formula, that type
is the bill.

## W2 (DD4), ANSWERED

The rule: write the mathematics once at a generic carrier and instantiate it.

**KEPT, AND IT IS WHY THE OBLIGATION IS 18 LINES.** `stage-shape`
(`Probe590.agda:77-87`) is written at an ABSTRACT predicate `P : V ℓ → Ω` and
mentions no code, no injection and no L-set. `stage-of-code`
(`Probe590.agda:179-182`) is one instantiation of it. A second consumer that
needs an ordinal out of a truncation takes `stage-shape` and writes only its own
predicate. **The generic form is `L.Stage.leastOrd`'s and is already in `src/`,**
so nothing new was written at the generic carrier and nothing needs to move
there.

## A PROPOSAL, NOT AN ACTION

`dev/literature/truncation-and-selection.md:285-302` is the checklist for exactly
this stall. Its item 4 (`:297-299`) names `leastOf`
(`src/L/WellOrder/Base.lagda.md:158-160`), and `leastOf` takes an `SWO A`
(`src/L/WellOrder/Base.lagda.md:158`), which asks trichotomy of the WHOLE carrier
type. **The ordinals are not a type here. They are the sub-class `IsOrd` of
`V ℓ`, and `V ℓ` carries no `SWO`**, so item 4 as written does not fire at
`StageOfCode`. The tree's class-level analogue is `L.Stage.leastOrd`
(`src/L/Stage.lagda.md:149-153`), which carries the ordinality as a side
condition instead of in the carrier, and the checklist does not name it. **I did
not edit the digest: it is outside this task's write scope.** The owner or the
mathematician may want one more row on that checklist.

## RUNS AND CALIBER

`GHCRTS=[-A64m -I0 -M8g]`, set by the program on this pane. **I did not set it.**
One Agda process at a time.

| run | file | exit | real | max RSS |
|---|---|---|---|---|
| `runs/w3-1.out` | `runs/W3.agda` | 0 | 0.95 s | 284.7 MB |
| `runs/p-1.out` | `Probe590.agda` | 42 | 9.44 s | 1063.5 MB |
| `runs/p-2.out` | `Probe590.agda` | 42 | 1.53 s | 404.6 MB |
| `runs/p-3.out` | `Probe590.agda` | 0 | 1.75 s | 405.7 MB |
| `runs/p-final.out` | `Probe590.agda` | 0 | 2.01 s | 405.7 MB |
| `runs/w3-final.out` | `runs/W3.agda` | 0 | 0.93 s | 279.3 MB |

`runs/p-1.out` is the only cold run and it includes `LJ-1-583.Probe583`,
`LJ-1-576.Probe576`, `L.CodedShift` and `L.Absorption`. No heap wall at any
point.

## RATIO BAR

Not applicable. This task writes one raw `.agda` probe and no `.lagda.md` master,
so the in-fence line count of the write scope is 0 and the bar cannot fire.

## ARCHIVE USED

- `archive/dev/JOURNAL-archived.md` **READ AND USED.** At
  `archive/dev/JOURNAL-archived.md:3645`: "`L.Stage`'s descent is now `leastOrd`;
  `bound2` moved from". This is the record of the move that made this task an
  instantiation, and it is why I looked below `L.Reflect` rather than inside it.
  Also `:1442`, "truncation wall on the naive descent, cured by the least-witness
  pattern the re-home probe", which is the same cure at an earlier site.
- `archive/dev/LJ-dispatch-index.md` **READ.** At `:387`: "| LJ-1.333 | Item 2 at
  the cheaper truncation | STATEMENT-LEVEL. CHEAPER TO PROVE, HARDER TO
  UNTRUNCATE | The band is the exact complement of the only canonicalizer. Five
  attempts were not unlucky |". Read as a warning that an untruncation can be the
  hard half. It did not apply: this one is a canonicalization by least ordinal
  and it cost nothing.
- `archive/dev/JOURNAL.md` **READ, NOT USED.** At `:1353`:
  "`dev/literature/truncation-and-selection.md:311-314` but sits at `:307-310`;".
  Its hits are line-number corrections to that digest and not mathematics, so I
  read the digest at its live line numbers instead.
- `archive/dev/DD-archived.md` **READ.** At `:38`: "**A PROVABILITY PROBE
  SURVEYS THE LITERATURE FIRST, and the survey and the probe are ONE task.**"
  That is DD28, and it orders the survey ahead of the Agda. Followed: `truncation-and-selection.md`
  section 4's checklist was read before the obligation was written, and it is what
  told me to look for a well-order plus a propositional payload.
- `dev/ARCHIVE.md` **NOT USED, DECLINED.** It is the archive registry
  (`dev/ARCHIVE.md:1`). This task retires no module and moves nothing, so it has
  no row to write and nothing to read there.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md` **READ AND USED, AND IT IS THE
  ONE THAT MATTERED.** Section 4 is the checklist for a stall on a truncation.
  At `:289`: "1. **Is the goal a proposition?** Then `PT.rec` applies and there
  is nothing to". **Item 4 at `:297-299` is the route this task took**, one class
  level up from the `leastOf` it names. See "A PROPOSAL" above.
- `dev/literature/devlin-II5.md` **NOT READ, DECLINED.** Devlin II.5 is the
  definability chapter. This task builds no definable set and writes no formula.
  The one place a formula was in question is `ViaSearchBounds`, and that route
  was rejected on the frame and not on the definability.
- `dev/literature/digest.md` **NOT USED, DECLINED.** Grepped for `leastOrd`,
  `least ordinal` and `least stage`: no hit. Nothing to take from it here.
- `dev/literature/terms-2026-08.md` **NOT USED, DECLINED.** Its two hits (`:328`,
  `:384`) are about cardinals as least ordinals of their cardinality. This task
  picks a least ordinal carrying a code, not a cardinal, so the term does not
  apply.
- `dev/literature/geology.md` **NOT READ, DECLINED.** Set-theoretic geology is
  about grounds and mantles. Nothing in this task leaves `L`.

## WORKING TREE

Everything I wrote is under `agents/tasks/LJ-1-590/` and inside the brief's write
scope. `git status --porcelain` reports one untracked directory and nothing else.
`agents/tasks/LJ-1-590/LJ-1.590.md` and `agents/tasks/LJ-1-590/.pod` are the
program's own and I did not touch them.

- `agents/tasks/LJ-1-590/Probe590.agda` (220 lines)
- `agents/tasks/LJ-1-590/runs/W3.agda` (71 lines)
- `agents/tasks/LJ-1-590/runs/run.sh` (copied from `[LJ-1.583]`, path retargeted)
- `agents/tasks/LJ-1-590/runs/*.out` (six runs)

**No `review-of-*.md` is written: this is a GO and not a stop.** Nothing under
`src/` is touched. Nothing is committed and nothing is pushed.
