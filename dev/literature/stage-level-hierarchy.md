# Stage, level and hierarchy around the constructible universe

This note records the evidence behind three terms that must remain distinct in the prose. It does not infer absence from an unsuccessful search.

## The mathematical distinction

- The **constructible hierarchy** is the whole ordinal-indexed family \(\{L_α \mid α \in \mathrm{On}\}\).
- A **stage** is one step \(L_α\) in that construction.
- A **stage index** is the ordinal \(α\), rather than the set \(L_α\). In `L.Stage`, `stage x hx` returns this ordinal and `stage-mem` proves `x ∈ Lset (stage x hx)`.
- The project's **layer** predicate `isLayer` describes a separate closure property. It should not be identified with either the entire hierarchy or the ordinal returned by `stage`.

## Direct evidence and composed renderings

Yasuda's set-theory lecture defines the Japanese **L-階層** \(\{L_α \mid α \in \mathrm{ON}\}\), gives the zero, successor and limit clauses, and then calls their union the **構成可能宇宙**. This directly supports `constructible hierarchy = 構成可能階層` and the distinction between the family and its members:

- Naohiro Yasuda, *The computation of HOD^{L(R)}*，数学基礎論若手の会 2021, PDF p. 8: https://www2.kobe-u.ac.jp/~tk/jp/workshop/slides/wakate2021_yasuda.pdf

An article in *科学基礎論研究* likewise introduces the **構成可能階層** as an analogue of the cumulative hierarchy and begins its recursive definition with \(L_0\). This is a second direct Japanese occurrence:

- *科学基礎論研究* 39(2), constructible-hierarchy discussion: https://www.jstage.jst.go.jp/article/kisoron/39/2/39_KJ00007978404/_pdf

A paper in *逻辑学研究* uses Chinese **层级** for a transfinite recursively indexed Kleene hierarchy. This attests the mathematical hierarchy stem, but it is not a direct occurrence of **可构造层级** or an account of \(L_α\):

- *逻辑学研究* 2025(4), discussion of the Kleene hierarchy: https://studiesinlogic.sysu.edu.cn/sites/default/files/2025-08/1674-3202%282025%29-04-0088-18.pdf

Accordingly，**可构造层级** is recorded as a pattern-based Chinese compound. The renderings **阶段 / 段階** for an individual stage and **阶段索引 / 段階の添字** for its ordinal index are also descriptive compounds. The sources above do not directly attest those CJK expressions as names for \(L_α\) or \(α\).
