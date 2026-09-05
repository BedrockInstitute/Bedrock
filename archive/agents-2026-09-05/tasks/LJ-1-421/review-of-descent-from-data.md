# Review of `descent-from-data`

GO. The term is `agents/tasks/LJ-1-421/Probe421.agda:225-263`. It
typechecks. The conclusion is `sq x`. There is no `∥ ∥₁`.

W3 (`d-is-kappa`, `:144-150`) applies `[LJ-1.413]`'s `descent-data` at
`d := κ`. The only argument that fails to elaborate from the tree is
the DATA arrow, at type `⟪ fst x ⟫ ↪ ⟪ fst (κL x ox) ⟫`
(`runs/w3-from-tree.out:2-7`). `κ-injL` is truncated
(`Probe406.agda:88-89`). `kappa-arrow-data` (`:214-216`) is that
arrow as data.

Case three spends `init-at-kappa` at `[LJ-1.406]`'s delivered type
(`Probe406.agda:180-185`). Case four spends `d := κ`. There is no
`amb-to-coded`, no `coded-descent` and no `IsCardinalL` in the
telescope.

The campaign's residue is one untruncated arrow at a named ordinal,
not a coding problem.
