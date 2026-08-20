# cubical-bonak

Cubical Agda ports of the Bonak νSet / νGpd construction
(indexed construction of semi-simplicial and semi-cubical sets and
their groupoid structure), kept on branches / worktrees:

- `main` — the canonical tower (`Bonak/νSet.agda`): **fillers-only
  storage** with relative `(p , k)` indexing (V4 — only the fillers
  are stored; every other notion is a function in one mutual block; no
  Deps records), a **checked termination argument** via the fuel
  column (no `TERMINATING` pragma), and **PathP-shaped coherences**
  (V2 — dependent paths over the frame coherence; no statement
  contains a subst).  Status narrative: `V4-REPORT.md`.
  The **νGpd storey** (`Bonak/νGpd.agda`) sits on the same base:
  HGpd-valued frames/layers/paintings, the coh2 storey, and one
  truncation site (`isGroupoid→Cube`); termination stays checked
  (no pragma, `--termination-depth=4`); its pasting kit is
  `Bonak/GpdLemmas.agda`, whose fused closing lemma `coh2Layer-cubeP`
  checks the layer 2-coherence once over abstract families.
  Cost analyses: `CONV-COST.md` (the kit's conversion profile),
  `DEADCODE-COST.md` (Agda's interface-pass overhead).
- `globular` (worktree `../globular`) — **V1, direct mirror** of the
  Rocq construction (`theories/νSet/νSet.v` + `νGpd.v` at bonak
  master): Deps* records, Extension data types, Id-shaped coherences
  (`subst`/`Σ≡`), the νGpd storey up to the rung-2 conversion wall,
  and the `GpdLemmas` pasting kit (`rew-coh2Layer` proved).
- `fillers-only` (worktree `../fillers-only`) — the V4 build line
  `main` is based on: same storage and fuel discipline, Id-shaped
  coherences.
- `pathp` (worktree `../pathp`) — **V2, PathP-native** on V1's
  storage: coherences stated as (nested) `PathP` along the lower
  coherences applied to interval variables, in the shape Astra's
  permutahedron coherences predict; no PathOver kit, no glue lemmas.
- `rew` (worktree `../rew`) — **V3, groupoid-rew** on V1's storage:
  coherences stated pointwise on transported inhabitants (nested
  `subst` chains, no path composites), per the validated
  `RewTrick.agda` discipline — funExt round-trips definitionally, one
  interface lemma per level shift.
- `conv-cost` (worktree `../conv-cost`) — experiment line off `main`:
  restructurings of the GpdLemmas kit aimed at cutting its boundary
  conversion count (see `CONV-COST.md`, "Directions").

Self-contained: builtin cubical primitives only (`Bonak/Prelude.agda`),
no external library. Toolchain: Agda 2.8.0,
flags `--cubical --prop --guardedness` (set library-wide in
`cubical-bonak.agda-lib`).

Feasibility probes live in `probes/` (P00: the three flags coexist;
Prop-valued `leR` is definitionally irrelevant in index positions;
coinductive records check).

Reference material (separate repos): the Rocq Bonak source
(`theories/νSet/νSet.v`, `νGpd.v` at
<https://github.com/artagnon/bonak>), its Lean 4 mirror
(<https://github.com/olympichek/bonak-lean>), the
PathP-self-similarity design note (V2/V3), and the RewTrick +
Coh2Frame probe collection.
