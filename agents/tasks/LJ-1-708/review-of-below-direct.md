# review-of-below-direct: a STATED NO-GO, with the residual measured

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.708
obligation: agents/tasks/LJ-1-708/Probe708.agda::below-direct
verdict: **NO-GO on the closed term from the licensed triple.**
`below-direct`, of the type `Below` at `[LJ-1.697]`'s frame
(`agents/tasks/LJ-1-697/Probe697.agda:72-74`), is not inhabited, and
the reason is structural: of `ord∈Lset→∈`, `Lset-mono` and `succλ`,
NO row concludes a stage membership out of anything but another stage
membership or a plain carrier membership, so every assembly bottoms
out in a judgment no licensed rule produces.

The witness meter reads `missing`, exit 42,
`1 UNRESOLVED of 1, 3.27 s, probe_red=False`
(`runs/meter-obligation.out`). The probe is green and carries no hole
(`runs/p-2.out` first green; median 3.14 s over `runs/recheck-1.out`,
`runs/recheck-2.out`, `runs/recheck-3.out`). The obligation name is
absent from the probe by design, as at `Probe679.agda` and
`Probe697.agda`.

**THIS IS NOT A REFUTATION OF `Below`.** The type is true through the
door: `[LJ-1.707]` closed the through-door assembly GO on its two
keystone hypotheses (`agents/tasks/LJ-1-707/lj-1.707-report.md:9-11`),
and nothing here contradicts it. What is measured is only that the
three door-free rows do not place the table.

The critic reads this file. It does not close the task.

---

## 1. THE ATTEMPT, MEASURED

`runs/cand-1.agda.txt:69-71` is the honest maximal assembly: it aims
the only rule in the licensed triple whose conclusion is a stage
membership, `Lset-mono`
(`src/L/Constructible.lagda.md:365-366`), straight at the goal:

    below-direct δ oδ =
      Lset-mono {α = W3.step 3 (fst δ)} {β = _} _ _

The run records exactly three unsolved metas at those three slots
(`runs/cand-2.out:6-8`). No other rule applies, so this is the whole
distance:

1. the index slot `β : S`,
2. the index-membership premise `⟨ β ∈ˢ Lset (step 3 (fst δ)) ⟩`'s
   smaller twin `⟨ β ∈ˢ step 3 (fst δ) ⟩`, itself unproduced,
3. the base membership `⟨ fst (hierL (fst δ) (δ .snd) oδ) ∈ˢ Lset β ⟩`,
   which is `Below` shifted down one step, and so recurses forever:
   each descent needs an earlier base stage membership, and there is
   no floor below which the triple can produce one.

## 2. WHAT EACH LICENSED ROW ACTUALLY PRODUCES

| row | conclusion | producer of fresh stage membership? |
|---|---|---|
| `ord∈Lset→∈` (`src/L/Ordinal/Stages.lagda.md:265-268`) | `⟨ x ∈ˢ α ⟩`, plain | NO. Downward, index-side |
| `succλ` (`agents/tasks/LJ-1-679/Probe679.agda:64`) | `⟨ sucV d ∈ˢ lam ⟩`, plain | NO. Climbs inside `lam` only |
| `Lset-mono` (`src/L/Constructible.lagda.md:365-366`) | `⟨ x ∈ˢ Lset α ⟩` | Only FROM `⟨ x ∈ˢ Lset β ⟩`. Extends, never starts |

So the brief's W3 question has a measured answer: NEITHER
`ord∈Lset→∈` NOR `succλ` is individually short, because neither
belongs to the class of rules that could supply rows 2 or 3 above.
What is missing is not one lemma's strength. It is a BASE case: any
producer whatsoever of a first stage membership for a fresh set.
Every such producer the tree owns fires the door.

## 3. EVERY PRODUCER IN THE TREE FIRES THE DOOR OR IS OUT OF LICENSE

A survey over `src/` found these producers of stage memberships:

- `𝒟ₒ-intro` (`src/L/Constructible.lagda.md:301-304`), the door
  itself, excluded by this task by name.
- `Lset-in` (`src/L/Constructible.lagda.md:329`), whose premise is
  `⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩`: no door-free producer among the triple.
- `stage-mem` (`src/L/Stage.lagda.md:188`): places a constructible
  set at ITS OWN earliest stage. It carries its own license problem,
  and even granted, it would place `hierL δ` at `stage (hierL δ) _`,
  whose bound under `step 3 (fst δ)` is exactly `[LJ-1.705]`'s bill
  (`agents/tasks/LJ-1-707/Probe707.agda:60-63` names that bound as a
  separate hypothesis). It rescues nothing here.
- `Lset∈suc` (`agents/tasks/LJ-1-697/runs/W3.agda:42-44`), green, and
  fired ON `𝒟ₒ-intro` at line 44. Taking it would smuggle the door in
  through a preproven lemma, so the probe's using-list
  (`Probe708.agda:65-66`) deliberately does not open it.
- the StageBound lemmas (`src/L/StageBound.lagda.md:122`): not
  licensed, and they carry their own collection data anyway.

No sixth producer exists for `⟨ t ∈ˢ Lset w ⟩` shapes. The boundary
rows are complete.

## 4. WHAT TRANSFERS

To `[LJ-1.704]`: this NO-GO does not weaken the door route, it makes
it load-bearing. The identification keystone and the bound keystone
are not conveniences. Given the producer census in section 3, some
door-firing fact MUST enter any placement argument for the table.
Fund both.

To any future door-free ambition: do not re-attempt `below-direct`
from these three rows, nor from any subset-superset of them that still
excludes door-fired lemmas. Fund a new producer first, as its own
task, priced against section 3's census.

Not owed: a C-42 sweep. Nothing was refuted. `Below` is uninjured;
only this route's toolkit is measured empty for it.
