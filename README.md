# cubical-bonak

Cubical Agda ports of the Bonak νSet / νGpd construction
(indexed construction of semi-simplicial and semi-cubical sets and
their groupoid structure), in three variants kept on branches /
worktrees:

- `main` — **V1, direct mirror** of the Rocq construction
  (`theories/νSet/νSet.v` + `νGpd.v` at bonak master): HSet with
  explicit `isSet`, `leR` in `Prop` (mirroring Rocq's `SProp`),
  TypeBlock fixpoints, Deps* records, Extension data types, and the
  coinductive `νSetFrom`.
- `pathp` (worktree `../pathp`) — **V2, PathP-native**: coherences
  stated as (nested) `PathP` along the lower coherences applied to
  interval variables, in the shape Astra's permutahedron coherences
  predict; no PathOver kit, no glue lemmas.
- `rew` (worktree `../rew`) — **V3, groupoid-rew**: coherences stated
  pointwise on transported inhabitants (nested `subst` chains, no
  path composites), per the validated `RewTrick.agda` discipline —
  funExt round-trips definitionally, one interface lemma per level
  shift.

Self-contained: builtin cubical primitives only (`Bonak/Prelude.agda`),
no external library. Toolchain: Agda 2.8.0,
flags `--cubical --prop --guardedness` (set library-wide in
`cubical-bonak.agda-lib`).

Feasibility probes live in `probes/` (P00: the three flags coexist;
Prop-valued `leR` is definitionally irrelevant in index positions;
coinductive records check).

Reference material: `~/bonak/master` (Rocq source),
`~/bonak/lean` (Lean 4 mirror precedent),
`~/bonak/notes/PathP-self-similarity.md` (V2/V3 design),
`~/bonak/cubical-probes/` (RewTrick + Coh2Frame probes).
