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
- `conv-cost` (worktree `../conv-cost`) — the kit-cost experiment
  line off `main`; its findings (per-binding section overhead, the
  staged telescope, flat `junctionP`) are adopted on `main` and
  written up in `CONV-COST.md`, and the branch keeps the probes and
  raw numbers (`CONV-EXP-NOTES.md`).

Self-contained: builtin cubical primitives only (`Bonak/Prelude.agda`),
no external library. Flags `--cubical --prop --guardedness` are set
library-wide in `cubical-bonak.agda-lib`, so no file needs its own
`OPTIONS` beyond `--termination-depth`.

## Toolchain

Agda 2.8.0 checks the tree, but the preferred toolchain is an Agda
2.9.0 nightly: it carries the fix for the interface pass analysed in
`DEADCODE-COST.md`, which is the difference between a ~39 min and a
~5.5 min cold build of the νGpd storey. Hackage carries releases only,
so the nightly is built from source: `cabal.project` holds nothing but
the URL of Agda's rolling `nightly` tag, and building it from the
repository root installs the compiler.

```sh
cabal install exe:agda -w ghc-9.12.2 --program-suffix=-nightly \
      --installdir=~/.local/bin --overwrite-policy=always
```

That leaves `agda-nightly` on the PATH beside whatever `agda` is.
`-w` is optional and picks a GHC whose package store is already
populated (Agda 2.9.0 supports 9.2.8 to 9.14.1); the tag moves with
master, and `cabal.project` says how to pin a commit instead.
`install` also builds `agda-mode` and the
`agda-tests` executable with its tasty dependencies (14 units against
2); to skip them, `cabal build exe:agda` with the same flags and
symlink `cabal list-bin exe:agda` instead. Interfaces are cached per
Agda version under `_build/<version>/agda/`, so a release and a
nightly can be used alternately without invalidating each other's
caches.

## Building

```sh
agda --build-library
```

checks every module the `.agda-lib` includes. To check one root
instead: `agda probes/Examples.agda` is the νSet gate and
`agda probes/ExamplesGpd.agda` the νGpd gate, each pulling in what it
imports. `--parallel` / `-j` exists on 2.9.0 but loses on this tree —
6 min 42 s against 5 min 34 s sequential for the full library, the
chain `Prelude → … → GpdLemmas → νGpd` being linear (cf.
agda/agda#8477).

Feasibility probes live in `probes/` (P00: the three flags coexist;
Prop-valued `leR` is definitionally irrelevant in index positions;
coinductive records check).

Reference material (separate repos): the Rocq Bonak source
(`theories/νSet/νSet.v`, `νGpd.v` at
<https://github.com/artagnon/bonak>), its Lean 4 mirror
(<https://github.com/olympichek/bonak-lean>), the
PathP-self-similarity design note (V2/V3), and the RewTrick +
Coh2Frame probe collection.
