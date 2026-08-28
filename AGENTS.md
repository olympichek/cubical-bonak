# Agent guide

Orientation and working conventions for AI agents (and anyone else)
contributing to this repository. The construction itself and the
toolchain are described in `README.md`; this file covers layout,
branches, build discipline, and writing preferences.

## Layout

- `Bonak/` — the library: `Prelude`, `NatRew`, the νSet tower
  (`νSet.agda`), the νGpd storey (`νGpd.agda`) and its pasting kit
  (`GpdLemmas.agda`).
- `examples/` — the compute gates. `Examples.agda` instantiates the
  νSet tower and defines `frame4` (with `SemiSimplicial4` and its
  point prefix `pt4`); `ExamplesGpd.agda` does the same for νGpd with
  `frame5`. Printing (normalizing) `frame4` and `frame5` is done here:
  each normalizes with every dimension argument closed, so the tower's bodies at the
  lower dimensions must reduce away, which is what makes these files
  the gates.
- `agents/probes/` — feasibility probes: small self-contained files
  that isolate one design question each (flag coexistence, `≤`
  transport, the V4 termination and dimension-column experiments).
  Add new probes
  here rather than experimenting inside `Bonak/`.
- `agents/notes/` — working notes and status reports.
  `PORTING-NOTES.md` is the running record and resume kit — read it
  before touching `Bonak/`, and record durable findings there.
  `V4-REPORT.md` narrates the fillers-only design, `CONV-COST.md` the
  pasting kit's conversion profile, `DEADCODE-COST.md` the Agda
  interface-pass overhead, `PARALLEL-BUILD.md` the `--parallel`/`-j`
  measurement.

## Branches and worktrees

Alternative designs are kept on branches, usually checked out as
sibling worktrees (`git worktree list` shows them):

- `main` — the canonical tower: fillers-only storage (V4), the
  dimension-column termination argument, PathP-shaped coherences, the
  νGpd storey.
- `globular` — V1, direct mirror of the Rocq construction: Deps*
  records, Extension data types, Id-shaped coherences.
- `fillers-only` — the V4 build line `main` is based on: same storage
  and dimension discipline, Id-shaped coherences.
- `pathp` — V2, PathP-native on V1's storage (no PathOver kit, no glue
  lemmas); design note `DESIGN-V2.md` in its root.
- `rew` — V3, groupoid-rew on V1's storage: coherences stated
  pointwise on transported inhabitants; design note `DESIGN-V3.md`.
- `conv-cost` — the kit-cost experiment line off `main`; findings are
  adopted on `main`, the branch keeps the probes and raw numbers
  (`CONV-EXP-NOTES.md`).
- `unindexed-prefix` — the prefix loses its index and the file loses
  `--rewriting`.
- `display-internalization` — further experiment line off `main`.

Work intended for `main` should not be developed on the experiment
branches; port findings back via `agents/notes/PORTING-NOTES.md`.

## Building and babysitting

- Gates: `agda examples/Examples.agda` (νSet) and
  `agda examples/ExamplesGpd.agda` (νGpd); `agda --build-library`
  checks everything. Prefer `agda-nightly` (2.9.0) — see README for
  why and how it is installed. Build sequentially: `--parallel`/`-j`
  loses on this tree (`agents/notes/PARALLEL-BUILD.md`).
- Heavy files legitimately spend minutes inside a single definition
  (`mkCohPainting` and the νGpd kit are conversion-bound), with no
  output in between. Do not conclude a check is wedged from silence;
  time it and compare against the numbers in `agents/notes/`.
- Interfaces are cached per Agda version under `_build/<version>/`.
  A rerun that finishes instantly is replaying interfaces; for timing
  claims, state whether the measurement is cold or hot and which Agda
  checked it.
- `UnsupportedIndexedMatch` warnings from the Extension inductives are
  expected and benign here (all scrutinees are literal constructors).
- Some proof terms are consumed definitionally downstream (see the
  load-bearing design decisions in PORTING-NOTES): do not reshape such
  proofs, reorder their clauses, or change how they are abstracted,
  even when a shorter proof checks.

## Writing preferences

For code comments, PR descriptions, and durable documentation:

- Check every technical claim against the code or a cited source.
  Support measurable claims, especially performance claims, with
  concrete evidence and enough context to interpret the comparison.
- Explain genuine insights — invariants, rationale, proof
  dependencies, design constraints. Do not restate what names, types,
  or the surrounding implementation already say.
- State an idea once, at the narrowest scope that serves every
  relevant reader; remove nearby restatements.
- Describe the code as it exists. No implementation history, no
  references to earlier versions or anticipated refactors, and no
  references to the Rocq/Lean/Agda-vanilla implementations in code
  comments — relationships to those belong in PR descriptions, which
  is also the place to credit their authors.
- Plain English or established terminology; no unusual metaphors or
  ambiguous shorthand; avoid rhetorical "not X, but Y" contrasts
  unless the distinction is itself technical.
- PR descriptions: focus on what the change introduces, match length
  to scope. Include axiom dependencies, computation behavior, and
  performance tradeoffs when they affect how the result should be
  understood. Do not reference local checkouts or machine-specific
  paths.
- Anything going to GitHub and viewed from it — PR descriptions,
  issue descriptions, `README.md` and other Markdown GitHub renders —
  is not hard-wrapped; GitHub handles the wrapping. Local notes
  (everything under `agents/notes/`) are hard-wrapped.
