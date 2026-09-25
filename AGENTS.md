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
  each normalizes with every dimension argument closed, so the tower's
  bodies at the lower dimensions must reduce away, which is what makes
  these files the gates.
- `agents/probes/` — feasibility probes: small self-contained files
  that isolate one design question each (flag coexistence, `≤`
  transport, the V4 termination and dimension-column experiments).
  Add new probes here rather than experimenting inside `Bonak/`.
- `agents/notes/` — working notes and status reports.
  `PORTING-NOTES.md` is the running record and resume kit — read it
  before touching `Bonak/`, and record durable findings there.
  `V4-REPORT.md` narrates the fillers-only design, `CONV-COST.md` the
  pasting kit's conversion profile, `DEADCODE-COST.md` the Agda
  interface-pass overhead, `PARALLEL-BUILD.md` the `--parallel`/`-j`
  measurement, `NIGHTLY-TOOLCHAIN.md` the cabal mechanisms that
  cannot drive the nightly compiler build (why there is no
  `cabal.project`).

## Branches and worktrees

- Each worktree's directory name must match its checked-out branch. Keep `main/` on `main` and each experiment's worktree on its matching branch.
- Do not switch an established worktree to another branch to start a task: use or create the matching worktree with `git worktree add`, specifying the intended base explicitly when creating a branch.
- Before editing, check `git branch --show-current` and `git worktree list`. Report and resolve any mismatch before development, preserving uncommitted and ignored working files; do not use a mismatched checkout's `HEAD` as the implicit base for new work.

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

## Code style

- Code lines may run to ~90 columns; comments stay wrapped at ~72.
  Keep the final arguments of an application on the same line as the
  rest of the call rather than dangling on a short continuation line;
  when an expression must break, break before a subexpression (an
  opening parenthesis starts its own line, as with `(compPathP` in
  νGpd's coh-layer), never after one.
- Iterated successors are written with the postfix pattern synonyms
  `_+1` … `_+4` from Bonak.Prelude: `(n +3)`, `(p + k +2)`. They must
  stay pattern synonyms — a defined function in their place hides the
  constructors from the termination checker's call matrices and the
  mutual blocks stop checking.
- The bound lemmas are applied with explicit indices
  (`le-trans s r k Hs Hr`, `le-up q k Hq`). The implicit-argument
  operators `_↕_`/`↑_`/`↓_` in Bonak.LeProp fail inference at tower
  call sites: `_≤_` is a defined function, so Agda cannot recover the
  bounds from a proof's type.

## Writing preferences

For code comments, PR descriptions, and durable documentation:

- Check every technical claim against the code or a cited source.
  Cite non-obvious metatheoretic claims when a reference is useful.
  Support measurable claims, especially performance claims, with
  concrete evidence and enough context to interpret the comparison.
- Explain genuine insights — invariants, rationale, proof
  dependencies, design constraints. Do not restate what names, types,
  or the surrounding implementation already say.
- State an idea once, at the narrowest scope that serves every
  relevant reader; remove nearby restatements.
- Use heading markup only for a genuine section.
- Declarative documentation, especially code comments, describes the
  code as it exists and uses terminology consistent with the
  mathematical abstraction and surrounding development. Keep it
  self-contained: explain the current invariants and design directly,
  without requiring familiarity with earlier versions, other
  repositories, or anticipated refactors.
  Comparisons with another implementation do not belong in code
  comments because that implementation can evolve independently and
  make the comparison stale.
- Temporal documentation, including commit messages and pull request
  descriptions, records how and why the code changed. When work is
  ported from or inspired by another project, name that project, cite
  the relevant source, and credit its authors. Write from the positive
  perspective of what the change introduces; mention behavior that
  remains unchanged only when its preservation is important or
  particularly non-obvious.
- Plain English or established terminology; no unusual metaphors or
  ambiguous shorthand; avoid rhetorical "not X, but Y" contrasts
  unless the distinction is itself technical.
- Avoid excessive qualifications when a supported high-level claim is
  accurate enough. Distinguish mechanized results from mathematical
  consequences when necessary, without foregrounding irrelevant
  caveats.
- Do not reference files under `agents/` from code comments or
  `README.md`; they are working artifacts, not reader-facing support
  for the code or project overview.
- PR descriptions: focus on what the change introduces, match length
  to scope, and omit unaffected behavior and routine compilation or
  test commands that CI verifies. Explain the problem or context, the
  change, and its impact. Include axiom dependencies, computation
  behavior, and performance tradeoffs when they affect how the result
  should be understood. Focus on the high-level result and central
  proof architecture rather than inventories of supporting symbols.
  Discuss future work only when it adds useful context, and state its
  modality accurately. Pin remote links to a commit when a claim
  depends on an exact revision. Do not reference local checkouts or
  machine-specific paths.
- Anything going to GitHub and viewed from it — PR descriptions,
  issue descriptions, `README.md` and other Markdown GitHub renders —
  is not hard-wrapped; GitHub handles the wrapping. Local notes
  (everything under `agents/notes/`) are hard-wrapped.
