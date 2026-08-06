# Build constraints (archived from dev/PLAN.md section 7)

> **STATUS: SUPERSEDED.** Each constraint is enforced where it fires, which is why this restatement was retired: the single trusted gate and the import-closure audit are the build machinery (scripts/README.md, scripts/check-tree.py closure); heap caps and one-process-at-a-time are AGENTS.md and dev/ORCHESTRATION.md section 2 (dev/LESSONS.md C-12); a cold-check regression is a defect in the return checklist, dev/ORCHESTRATION.md section 6 step 2. Read it when the original numbered text of a build constraint is needed; dev/PLAN.md section 7 is now a numbered pointer that keeps every citation resolvable.

---

## 7. Build constraints (D10, binding)

Imported from the source's Makefile trust model (`../fol-reification/Makefile`,
WORKLOG §8.1) and adapted to Bedrock's rules:

1. **The trusted gate is one invocation.** `agda src/Everything.lagda.md`
   remains the single certificate: one call, obviously correct, never
   parallelized. Since Bedrock's whole tree is `--safe` and `Everything`
   imports all of it, this one invocation is the entire trust base.
2. **Parallelism is a warm-up layer, outside the trust base.** The parallel
   per-module build exists only to populate `.agdai` interfaces fast; the
   `Everything` invocation then revalidates hashes cheaply. Make's dependency
   edges are scheduling hints: a wrong edge can cause wasted work or a false
   red, never a false green.
3. **The one false-green mode is audited away.** A module missing from
   `Everything`'s import list is unchecked by the gate. An audit script
   asserts, on every check, that the import closure of `Everything` equals the
   set of `src/**/*.lagda.md` files.
4. **The dependency manifest is generated, never committed.** `gen-deps` runs
   in under a second, so the manifest is regenerated into `_build/` on every
   check and consumed from there.
5. **Cold-check wall-clock is a tracked budget.** Baseline numbers are recorded
   in §11 at every gate. Working ceiling: full cold check at or under **15
   minutes at `-j4`** on the reference machine (upstream proves the same
   mathematics fits in about 8.5). A merge that breaches the ceiling is
   blocked until triaged.
6. **Per-module discipline.** Per-module heap caps (the source settled on
   `-M6g`; revisit against measurements). A module exceeding roughly **120
   seconds** cold or its heap cap is a conversion blowup: triage with the
   source's WORKLOG §5 playbook before merging, and annotate any surviving
   countermeasure per the L0.0 rules.
7. **Serial fallback stays available.** A serial full-check target (single
   process, wide heap cap) is kept for dispute arbitration and for reproducing
   races, as in the source.
8. **Reference machine and `-jN` defaults are documented in the build
   config**, so budget numbers are comparable across time.
