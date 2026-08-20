# Conversion cost of the fused layer-2-coherence kit

`main` worktree, Agda 2.8.0, 2026-08-20.  The subject is the final
section of `Bonak/GpdLemmas.agda` — the ~60-parameter anonymous module
whose public member `coh2Layer-cubeP` closes `coh2-layer` — and why
checking it takes ~10 minutes even with interface-writing overhead
removed (see `DEADCODE-COST.md` for that separate cost).

**Result: the time is genuine type-checking, concentrated in the
junction-cell and stated-lateral group, and its driver is the number
of boundary conversions the pasting forces, not the size of any one
reduction step.**

## Mechanism

Each lateral face of the cube (`L₀`, `L₁`, `LC`, `LD`) is a vertical
composite of `∙slice` / `∙v` / `∙rP` squares — an hcomp tower stacked
on hcomp towers — and each carries a stated `SquareP` signature that
must be converted against the inferred boundary of that composite.
Each such comparison unfolds nested `hfill`s under interval
substitutions.  Two Agda facts make this expensive:

- The reducer has no memoization: `ReduceM` is a pure reader, so
  nothing caches normal forms across calls.
- Face decomposition re-reduces from scratch: `forallFaceMaps`
  substitutes the full context for every DNF face of a constraint and
  re-reduces the result, so subterms shared between faces are
  recomputed once per face of every square.

Because the module's families are abstract, every filler is neutral
and each individual reduction step is cheap — the abstractness is
what makes the kit feasible at all (in the tower's concrete Σ/Π
fibers the same pasting exhausted 35 GB without finishing).  What
remains is the sheer count of boundary conversions, which is set by
the pasting's depth: six junction cells (`junctionP.cell` instances,
each an `∙rP`-chain over `cong²Funct`, the `∙congF` bridge and
`assocP`), the four laterals, and the final `squarePOverCube`.

## Evidence

Localization was by binary search: truncating the module after each
internal binding and checking the prefix (patched binary,
interface-pass bypass, caps).  Prefixes up to the transported-slice
and base-square bindings each complete — the per-run growth from
270 s to ~400 s over fourteen prefixes is mostly fixed per-run
overhead — and the first prefix that includes the junction-cell /
stated-lateral group times out at 420 s.  The cost therefore sits in
that group, not in the telescope or the base-square layer.

Whole-file measurement after the kit was merged into `GpdLemmas.agda`:
the file checks in ~660 s elapsed, 10.5 GB peak residency, with the
interface pass bypassed — i.e. ~11 minutes of honest typing.  The
conversion success-cache patch (`AGDA_CONV_CACHE`, sound: caches only
meta-free successes that produced no constraints) observes a ~42% hit
rate on this workload, confirming the repeated-conversion profile.

The cost is paid once: the interface caches, and `Bonak/νGpd.agda` —
whose `coh2-layer-suc` is a single `coh2Layer-cubeP` application —
re-checks in ~2.5 min / 1.8 GB on stock Agda 2.8.0.

## Directions

Two restructurings should reduce the conversion count and are under
experiment on the `conv-cost` worktree (branch `conv-cost`):

- Flatten `junctionP.cell`'s three-stage `∙rP` chain into a single
  `comp′` over one hand-written `hfill` base, keeping its stated type
  so the six instances and the laterals are untouched.
- Name and state the intermediate composites inside `LC`/`LD` so each
  expensive conversion completes once and is reused by name.
