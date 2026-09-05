# LJ-1.13 report: the collapse at an extensional carrier

## 1. THE VERDICT

DELIVERED. The extensional injectivity half typechecks at 335 in-fence
non-blank lines. The delivered file measured 239 lines before. The added
content is 96 lines. The review's residue target is true. The proof
typechecks at the intended generality. No obstruction applies (D-10).

## 2. MY OWN ESTIMATE

I wrote this estimate before I wrote the induction. I estimated 95 to 105
in-fence lines. The added module is 96 lines. The estimate landed inside the
review's 80 to 200 bracket.

The basis was the delivered `Inj` module at
`src/V/Collapse.lagda.md:109-205`. That module is 97 lines. The extensional
case mirrors it directly.

The transitive proof uses `Xtr` four times. Three uses read a membership that
the code already carries. The fiber witness carries `b ∈ X` in `in⊆` and
`π∈-bwd`. The premise `z ∈ X` fires the hypothesis in `out⊆`. The `out⊆`
`Xtr` use is dead code. The one structural change is the final step. It uses
the carrier-restricted extensionality instead of the all-members
extensionality.

D-28 does not apply. The hypothesis is one module parameter. Two consumers
cannot pay for a kit. I wrote the extensional case directly.

## 3. THE STATEMENT

The extensionality hypothesis is a module parameter. It mirrors `Inj`'s
`Xtr`. The exact statement is:

```agda
isExt : S → Type (ℓ-suc ℓ)
isExt X = (x y : S) → x ∈ᵗ X → y ∈ᵗ X
        → ((z : S) → z ∈ᵗ X → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩)
        → ((z : S) → z ∈ᵗ X → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩)
        → x ≡ y
```

This is the structure extensionality of the carrier. Equal carrier members
have equal comparisons against the carrier members. Devlin derives this
property from `X ≺₁ L_α` at `dev2.txt:1173-1183`. `[LJ-1.14]` derives it
from the elementary embedding.

## 4. THE NUMBER

Before: 239 in-fence non-blank lines. After: 335 in-fence non-blank lines.
The added module is 96 lines. The ledger caliber counts non-blank lines
inside ` ```agda ` fences. The count reads the live working tree.

## 5. SECONDS

Before: 0.59 seconds real, exit code 0. After: 1.80 seconds real, exit code
0. The check used one process. The heap cap was
`GHCRTS="-A64m -I0 -M8g"`. The dependency interfaces were cached. The
module's own elaboration was cold.

The delta is +1.21 seconds. The noise rule is 0.5 seconds or 5 percent. The
delta is not flat. The rate is 0.0126 seconds per added line. That rate
matches the parameterized-content class in P-m.

## 6. WHAT THE J TOWER WOULD SUPPLY

The J tower must supply one certificate. It must prove `isExt X` for its
carrier `X`. Everything else is already delivered at the generic carrier.
`π`, `πX`, `πX-trans`, `π∈-fwd`, `unique`, and `fixes` need no tower content.
No statement mentions a stage. Per P-l, no presentation reaches the types.
The elementarity analogue replaces `X ≺₁ L_α`. `[LJ-1.14]` builds the L-tower
certificate. The J tower builds its own analogue.

The two cases share the module-parameter shape (P-h). They share the
statements `P`, `iso`, `Mostowski`, and `mostowski` as identical text. They
share the `∈`-induction skeleton. I did not factor a shared core. D-28 says
two consumers cannot pay for a kit.

## 7. WHERE MY READING OF 5.2 DIFFERS

My reading confirms the review's main claim. Devlin 5.2 collapses an
extensional carrier. The structure-extensionality argument is the
load-bearing change.

One detail differs. The review phrases the change as a new proof shape. My
reading finds the same induction. The induction target `P` is unchanged. The
two inclusion directions are unchanged. Only the membership witness sources
change. `in⊆` and `π∈-bwd` read `b ∈ X` from the fiber. `out⊆` fires on the
premise `z ∈ X`. The `Xtr` use in the delivered `out⊆` is dead code. Its
`bu` is computed but never used. The review's size class is right. The added
module is 96 lines. It is the same size class as `Inj`.

## 8. LITERATURE USED

- `_build/literature/dev2.txt:1173-1183`. The target statement. Devlin 5.2's
  proof reads: "Note first that X is extensional. For suppose that x,y∈X,
  x≠y. Then ... which means that for some z ∈ X, z ∈ x ↔ z ∉ y. Since X is
  extensional, by the Collapsing Lemma (1.7.1) there is a unique π and a
  unique transitive set M such that π: X ↠ M". The OCR text is garbled. I
  quote the readable parts.
- `_build/literature/dev2.txt:1302`. "Part (ii) follows immediately from
  1.7.1." This matches the delivered `fixes`.
- `dev/literature/devlin-errata.md`. WHY NOT: I searched for 5.2, Collapsing,
  and extensional. The only hit is MB p. 11 on the DB0 basis. No errata item
  touches 1.7.1 or 5.2. No step rests on a corrected claim.
- `dev/literature/digest.md`. WHY NOT: it pins the rud-route orthodoxy. It
  has no collapse content. It did not bear on this block.
- `[LJ-0.7]` output. WHY NOT: not available. I worked from the source text.

## 9. ARCHIVE USED

- `archive/rud-route/src/V/Collapse.lagda.md:227-349`. The retired route's
  collapse. Its `Inj` module also assumes `Xtr : isTrans X` at `:227`. The
  shape survives the route change in one sense. `[LJ-1.4]` ported the module
  verbatim. It does not survive in the sense that matters. The transitive
  injectivity never applies to the non-transitive hull. The new `InjExt`
  closes that gap.
- `_build/lj-1.4-report.md:1-102`. The delivered collapse record. It reports
  `Inj (Xtr)` and `fixes`. It measures 239 lines. Section 7.3 notes a
  consumer may need a different statement shape. This block delivers that
  shape.
- `archive/dev/TASKS-archived.md:74`. Row L3.32-T39 records the delivered
  Mostowski collapse.
- `dev/LESSONS.md`. P-h at `:174`. P-l at `:2264`. R-35 at `:782`. R-40 at
  `:929`. D-28 at `:1757`. D-10 at `:1316`. C-22 at `:2196`. I-5 at `:1196`.
  R-36 at `:808`. These decided the module parameter, the generic statements,
  the shallow witnesses, and the direct write.

## 10. WHAT I AM NOT SURE OF

1. The seconds use cached dependencies. Both runs had the same cache state.
   A true cold rate needs a whole-cone check.
2. The `isExt` shape is my choice. I chose two inclusions. A consumer may
   want one equivalence.
3. I did not derive `isExt` from elementarity. That is `[LJ-1.14]`'s task. I
   verified the proof needs exactly that certificate.
4. The J tower may want the `Mostowski` package at a concrete stage. The
   statements are generic per P-l. The instantiation is the tower's task.
