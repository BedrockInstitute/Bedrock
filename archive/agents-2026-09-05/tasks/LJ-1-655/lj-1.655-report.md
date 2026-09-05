# [LJ-1.655] report: is the chapter's own elementarity reachable at the collapse site

GO. Exit 0. `0 UNRESOLVED of 1` (`runs/witness-final.out:2`).

slot: `coder`. Written early as a skeleton and filled as each run landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-655/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M2g"` (the
wide tier), ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

The standing direction (`dev/pod/direction.md`) puts one SRC collection after
LJ-1 and not after `[LJ-2.5]`. This task is LJ-1 work, it lands nothing in
`src/`, and it starts neither the collection nor phase 3. No Boundary clause
is in conflict.

## 1. THE VERDICT

**ELEMENTARITY ARRIVES. It costs ONE pair, and the chapter already pays it.**

The obligation is at `agents/tasks/LJ-1-655/Probe655.agda:153`:

    elem-at-collapse :
        (n : ℕ) (φ : Formula CIso.I.SM n) (δ : Vec CIso.I.SM n)
      → (⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ (mapFo CIso.I.g φ) ⟩
          → ⟨ map HED.A.inL δ ASt.AbsL.⊨ᵐ (mapFo HED.A.inL φ) ⟩)
      × (⟨ map HED.A.inL δ ASt.AbsL.⊨ᵐ (mapFo HED.A.inL φ) ⟩
          → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ (mapFo CIso.I.g φ) ⟩)

It is `elem` composed with the collapse's own iso-invariance, and it says the
COLLAPSE's reading of a formula and the STAGE's reading of it agree, both ways,
at every arity. `elem` on its own speaks about `M` against `Lset lam`, which is
not the side anybody was stuck on.

**AND IT IS FREE AT THE CHAPTER'S OWN CONSUMER.** `Probe655.agda:300`:

    elem-at-collapse-free = AtChapterSite.W.elem-at-collapse

`AtChapterSite` (`Probe655.agda:267-293`) carries exactly the telescope of
`Devlin55.BoundedSubsetAt` (`src/L/BoundedSubset.lagda.md:1385-1396`) and
nothing more. It builds the collapse site the way the chapter builds it at
`:1520-1521`, then spends the chapter's OWN code pair by name. **No hypothesis
of this campaign's making survives in that term.**

## 2. THE CARRIER QUESTION (W3), AND IT IS FOUR `refl`s

W3 asked whether `A.SM`, the carrier `Elementary` quantifies over, is the
carrier the collapse site uses. **It is the same type, definitionally**, and
the estimate of 50 to 120 lines was high: the whole answer is five signatures
and five `refl`s (`Probe655.agda:106-126`).

    hull-agree    : HED.M ≡ M                        refl   (:106)
    code-agree    : HED.H.T.Code ≡ H.T.Code          refl   (:109)
    carrier-agree : HED.A.SM ≡ CIso.I.SM             refl   (:114)
    sat-agree     : HED.Mse._⊨_ δ φ ≡ CIso.I.⊨ᵐ δ φ  refl   (:119)
    stage-agree   : HED.ASt.AbsL ⊨ᵐ ≡ ASt.AbsL ⊨ᵐ    refl   (:124)

The reason is structural and not luck. `AtStage.AtM.SM` is
`Σ[ x ∈ S ] ⟨ x ∈ˢ M ⟩` (`src/L/Hull.lagda.md:165-166`) and `IsoInv.SM` is
`Σ[ x ∈ S ] ⟨ x ∈ˢ M ⟩` (`src/L/BoundedSubset.lagda.md:164-166`): one type,
written twice. The two SEMANTICS agree for the same reason: both are
`FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ M)) .At SM id`
(`src/L/Hull.lagda.md:168-169`, `src/L/BoundedSubset.lagda.md:174-176`).

**THE BRIEF'S PREMISE 4 IS CORRECT ON THE LINES AND WRONG ON THE CONCLUSION IT
INVITES.** `elem` is at `:759` and `HullStage` opens at `:903`, so it is above
the collapse site in the file. But being above it in the file buys nothing:
`elem` is not a top-level name. It sits inside
`HullElemDown.WithCode` (`src/L/BoundedSubset.lagda.md:667`, `:681`), two
parameterised modules deep. **Scope in this chapter is a TELESCOPE question,
never a line-number question**, and the telescope is what I measured.

## 3. WHAT ELEMENTARITY COSTS AT THE COLLAPSE SITE

**The outer module is free. The inner module is the whole price.**

`HullElemDown α ordα X X⊆L ∅∈α` (`src/L/BoundedSubset.lagda.md:667-668`) takes
the collapse site's telescope MINUS `succλ`, so the instance is built at the
site with **no new hypothesis at all** (`Probe655.agda:100`).

`WithCode` (`src/L/BoundedSubset.lagda.md:681-682`) then asks for two things:

    f      : A.SM → H.T.Code
    f-spec : (q : A.SM) → fst (H.T.val (f q)) ≡ fst q

**That pair is the entire price of elementarity at the collapse, and it is a
SELECTION problem, not a proof problem.** The hull is `sett Code (λ c → ...)`
(`src/L/Hull.lagda.md:115`) and its members carry only the TRUNCATED existence
of a code, `∥ Σ[ c ∈ Code ] (fst (val c) ≡ x) ∥₁`
(`src/L/Hull.lagda.md:338`). `⟪ Hull ⟫` is not `Code`: `⟪_⟫` reads a MONIC
presentation (`Cubical/HITs/CumulativeHierarchy/Properties.agda:220-221`) and
`val` is not injective, so the presentation cannot hand a code back. The way
out is the classical one: a least code under a well-order. That is
`CanonCode` (`src/L/BoundedSubset.lagda.md:463-500`), and it is why the pair
costs a counting.

**THE CHAPTER ALREADY PAYS IT.** `hedF` at `src/L/BoundedSubset.lagda.md:1651`,
`hedF-spec` at `:1655`, `HED` at `:1659` and `HEDC` at `:1665`, all inside
`Devlin55.BoundedSubsetAt`, and `HS = HullStage ...` sits at `:1521` in the
SAME module. The citation is machine-checked at `Probe655.agda:251-256`: the
three names are referenced, so the probe goes red if any of them moves.

**A SECOND FACT FALLS OUT OF THE CHAPTER'S OWN TEXT.** At `:1665` the chapter
feeds `hedF : (Σ[ x ∈ S ] ⟨ x ∈ˢ HS.M ⟩) → HS.H.T.Code` to
`HED.WithCode`, whose `f` is typed `HED.A.SM → HED.H.T.Code`. That line
typechecks in the tree today, so **`HS.M ≡ HED.M` and
`HS.H.T.Code ≡ HED.H.T.Code` were already load-bearing before this task.**
Section 2's `refl`s are not a new discovery; they are a fact the chapter
depends on and no report had written down.

## 4. WHAT THE ARRIVAL BUYS AT THE TWO NO-GOs

**`collapse-stage-agree` (`Probe655.agda:189`) is the form the two NO-GOs
named and never had.** At a parameter-free formula both relabellings are the
identity (`g-fixed` at `:172`, `inL-fixed` at `:178`), so the statement drops
to: the collapse and the stage agree outright.

    (n : ℕ) (φ₀ : Formula (⊥* {ℓ-suc ℓ}) n) (δ : Vec CIso.I.SM n)
      → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ (embed φ₀) ⟩
      ↔ ⟨ map HED.A.inL δ ASt.AbsL.⊨ᵐ (embed φ₀) ⟩

`[LJ-1.489]`'s verdict is at `agents/tasks/LJ-1-489/lj-1.489-report.md:100`:
"One line. The two sides cannot agree without elementarity. Left is", and again
at `:140`. The agreement now exists, at `Probe655.agda:304`, with no code
hypothesis left.

**`hood-complete-from-stage` (`Probe655.agda:224`) DISCHARGES `[LJ-1.653]`'s
HYPOTHESIS 2.** That predecessor took `HoodCompleteP φ₀`, "the hull believes
`Lset y` is the level at `y`", as a priced hypothesis
(`agents/tasks/LJ-1-653/Probe653.agda:230-233`). Elementarity reduces it to

    HoodCompleteStage φ₀   (Probe655.agda:215)

the SAME statement read at `Lset lam`. **That statement names neither `M` nor
`C.π`**: it is a fact about the level construction inside a stage, which is
what SECTION 4A of the chapter is about (`src/L/BoundedSubset.lagda.md:840`).

**I DID NOT BUY HYPOTHESIS 3, AND I WANT THE REASON ON THE RECORD RATHER THAN
GUESSED.** `[LJ-1.653]`'s `HoodSoundP` says the COLLAPSE is correct about
level-hood. Elementarity cannot reach it. Run the only available route:
`iso-inv-bwd` pulls a collapse-side satisfaction back to preimages in `M`,
`elem` carries it to the stage, and the stage's soundness returns
`v' ≡ Lset γ'` for the PREIMAGES. Turning that into `v ≡ Lset γ` is
`C.π (Lset γ') ≡ Lset (C.π γ')`, which is step 4 itself. **The chain closes on
its own tail.** Hypothesis 3 must come from `[LJ-1.653]`'s own Δ₀ leg
(`agents/tasks/LJ-1-653/Probe653.agda:159-162`), not from elementarity. So
of the two hypotheses that predecessor priced, elementarity kills one and
provably cannot kill the other.

## 5. THE PRICES

Every number below is from a run in `runs/`, under `-A64m -I0 -M2g`, one Agda
process, the `.agdai` deleted before each cold row.

| what | wall | file |
|---|---|---|
| FLOOR: PART 0 + PART 1 only (frame + W3) | 3.08 s | `runs/floor-clean.out` |
| FULL probe, cold | 8.08 s | `runs/final-4.out` |
| FULL probe, cold | 7.72 s | `runs/final-5.out` |
| FULL probe, cold | 6.86 s | `runs/final-6.out` |
| FULL probe, cold, final text | 6.58 s | `runs/final-8.out` |
| witness, `elem-at-collapse` | 3.62 s | `runs/witness-final.out` |

**I MEASURED THE FLOOR BEFORE I PROVED ANYTHING**, per the 2026-08-23 ruling.
The frame is 3.08 s and the whole proof adds under 5 s on top of it. Nothing
here is a heavy object and no restructuring was needed.

Size: 304 lines of file, 136 non-blank non-comment lines
(`agents/tasks/LJ-1-655/Probe655.agda`). W3 estimated 50 to 120 lines for the
carrier measurement alone; that part came to five signatures, and the extra
lines are PART 3 to PART 5, which the brief did not ask for and which are what
the next brief can spend.

**The ratio bar cannot fire on this return.** The probe is a raw `.agda` file
and carries no ` ```agda ` fence, so the divisor is 0 in-fence lines
(`grep -c '```agda'` returns 0).

## 6. WHAT THE NEXT BRIEF NEEDS

1. **Elementarity is a settled ingredient, not a residue.** `[LJ-1.652]` and
   `[LJ-1.653]` take it as a hypothesis. That hypothesis is FREE at the
   chapter's own consumer, and `Probe655.agda:300` is the term. A future brief
   should stop pricing it.

2. **THE REMAINING RESIDUE OF THE LEVELIN CHAIN IS `HoodSoundP` AND ONLY
   `HoodSoundP`.** `[LJ-1.653]` left two hypotheses; section 4 above kills
   hypothesis 2 and shows hypothesis 3 cannot be killed the same way. The
   next mathematical question is `[LJ-1.653]`'s Δ₀ leg
   (`agents/tasks/LJ-1-653/Probe653.agda:159-162`), not elementarity.

3. **The new target worth a dispatch is `HoodCompleteStage`**
   (`Probe655.agda:215`): does `Lset lam` satisfy the level-hood formula at
   `(Lset y , y)` for an ordinal `y` of the stage? It names no hull and no
   collapse, so it is a SECTION 4A question
   (`src/L/BoundedSubset.lagda.md:840-870`), and the chapter's `LevelHood0`
   already works there. I did not measure whether the chapter's existing
   level-hood terms discharge it; **that is the one thing this task leaves
   open, and it is open because the brief did not name it, not because it
   resisted.**

4. **A LAYOUT FACT WORTH CARRYING.** `elem` is unreachable from
   `HullStage` alone and reachable from `Devlin55.BoundedSubsetAt`. Any future
   statement wanting elementarity must be stated at the SECOND site. If a
   brief names `HullStage` or `HullStage.Condense` as the home of a term that
   needs elementarity, that brief is wrong by construction, and the two NO-GOs
   `[LJ-1.477]` and `[LJ-1.489]` are the measured cost of not knowing it: both
   worked at the `HullStage` cut (`agents/tasks/LJ-1-489/Probe489.agda:48`
   and `agents/tasks/LJ-1-477/Probe477.agda:40` both read "Telescope copied
   from src/L/BoundedSubset.lagda.md:903-916."), where the ingredient they
   named cannot be built.

## ARCHIVE USED

- **`archive/dev/JOURNAL-archived.md` READ.** `archive/dev/JOURNAL-archived.md:1756`:
  "consumer, the hull's full elementarity at hull parameters, which Devlin 5.5's bounded-subsets"
  This is the earlier record that Devlin 5.5 consumes the hull's FULL
  elementarity at hull parameters, which is the type `HullElemDown.WithCode`
  delivers and which section 1 above transports to the collapse.
- **`archive/dev/JOURNAL.md` READ.** `archive/dev/JOURNAL.md:328`:
  "**DD27 landed.** `[LJ-1.23]` re-indexed the hull by `Code`, 372 to 431 lines at"
  The hull being indexed by `Code` is exactly why `(f , f-spec)` of section 3
  is a selection problem rather than a projection.
- **`archive/dev/LJ-dispatch-index.md` READ.** `archive/dev/LJ-dispatch-index.md:44`:
  "| LJ-1.4 | Build: the Mostowski collapse | DELIVERED 239 lines | Ported from the archive's 181, plus Devlin 5.2(ii) which the archive lacked. Carrier-generic. Cold tree 133.39 s, exit 0 |"
  `Collapse` being CARRIER-GENERIC is why `CollapseIso M Mext` and
  `HullElemDown ... .A` land on one carrier: section 2's `carrier-agree`.
- **`archive/dev/ORCHESTRATION.md` DECLINED, not read.** It is the archived
  operating document of the retired orchestrator. It carries no statement about
  a carrier, a telescope or an Agda term, and a grep over it for `collapse` and
  `hull` returned nothing.
- **`dev/ARCHIVE.md` DECLINED, not read beyond the grep.** It is the register
  of RETIRED modules. A grep for `BoundedSubset` and `Hull` returned nothing,
  so nothing in this task's scope has been retired and the file has no bearing.

## LITERATURE USED

- **`dev/literature/devlin-II5.md` READ.** `dev/literature/devlin-II5.md:124`:
  "> elementary substructure of L_α which contains all elements of X."
  Devlin 5.3 states the hull's elementarity in `L_α`, which is the classical
  content of `A.Elementary` and confirms that the theorem is about `M` against
  the STAGE. That is precisely why `elem` alone does not serve a consumer at
  the collapse, and why section 1's composite with `iso-inv` is needed.
- **`dev/literature/truncation-and-selection.md` READ.**
  `dev/literature/truncation-and-selection.md:68`:
  "**The selection device is a definable well-order plus a universal guard.** The"
  This is section 3's price, stated in the literature's own terms: the code
  function `f` cannot come from the presentation, and the classical device is
  a least element under a definable well-order. `CanonCode`
  (`src/L/BoundedSubset.lagda.md:463`) is that device, and it is why the pair
  costs a counting rather than nothing.
- **`dev/literature/digest.md` OPENED AND DECLINED.**
  `dev/literature/digest.md:1`:
  "# Digest: the orthodox form of the rud route, pinned from the collected literature"
  It pins the RUD route, which is not the route this chapter takes. Nothing in
  it bears on a scope or carrier measurement in `L.BoundedSubset`.
- **`dev/literature/terms-2026-08.md` DECLINED, not read.** It is a
  translation-terminology file. This task writes no prose for translation and
  adds no term.
- **`dev/literature/glossary-review-2026-08.md` DECLINED, not read.** Same
  reason: it is a glossary review record, and this task proposes no glossary
  entry.
