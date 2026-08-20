# Agda's dead-code interface pass on large telescopes

`main` worktree, Agda 2.8.0, 2026-08-20.  The subject is
`Agda.TypeChecking.DeadCode.eliminateDeadCode`
(`src/full/Agda/TypeChecking/DeadCode.hs` in the Agda source), the
pass that runs when an interface (`.agdai`) is written, and its cost
on the fused layer-2-coherence module of `Bonak/GpdLemmas.agda`.  It
is independent of the type-checking cost documented in
`CONV-COST.md`.

**Result: on stock Agda 2.8.0 the pass costs wildly
disproportionately on modules with large dependent parameter
telescopes — it dominated the kit's share of the 53-minute cold build
— and it is pure implementation overhead: skipping it only makes
interface files larger.**

## What the pass does

Before serialization, Agda prunes the signature by a mark-and-sweep:
roots are the public definitions, primitives, `COMPILE`-pragma
definitions, all pattern synonyms, **all module-parameter sections**,
local builtins, rewrite rules and closed display forms; the traversal
(`goName`/`goMeta` over `namesAndMetasIn'`) walks the internal syntax
of everything reachable, and definitions and solved metavariables
never reached are dropped from the interface.

The sections-as-roots rule is deliberate over-approximation: pruning
section data crashed downstream importers in agda/agda#6931 (internal
error instantiating an empty parametrized module from another file)
and #7382 (`--save-metas` serialization crash, "Meta-variable not
found").  The root set therefore cannot easily shrink.

## Why it explodes here

The visited sets are keyed on `QName`/`MetaId` only — there is no
visited set at the level of term nodes — so every reached term is
walked as a tree, and heap sharing is invisible to the traversal.
A parameterized module is the worst case:

- every definition is section-lifted, so its internal type repeats
  the whole telescope prefix;
- the section telescopes themselves are roots;
- every metavariable solved while checking the telescope stores a
  type closed over its full context, and `goMeta` traverses both the
  instantiation and that stored type.

Total cost is roughly (definitions + solved metas) × (tree size of
the telescope prefix each carries), super-linear in the number of
parameters.  The kit's ~60-entry dependent telescope, whose late
parameters are large stated filler types, sits far outside the
distribution the pass was tuned for.

## Measurements

On a telescope-only prefix of the kit (60 parameters, trivial body):
76.9 s of the 77.9 s total run inside the `DeadCodeReachable`
profiling bucket, with actual typing at 0.3 s; each additional filler
parameter added ~90 s.  A locally patched binary with an env-guarded
bypass (`AGDA_NO_DEADCODE=1`: return all definitions, solved metas
and closed display forms unchanged) took the same prefix from 190 s
to 6.7 s, with identical downstream checking; under the bypass the
full kit is ~11 minutes of honest typing (see `CONV-COST.md`).
Skipping the pass is always sound — it only prunes — at the price of
larger interfaces.

## Upstream

Since the root set is pinned by #6931/#7382, the fix belongs in the
traversal: a visited set on term nodes (e.g. keyed by
`System.Mem.StableName`, or hash-consing) would make the cost
proportional to the shared DAG rather than the expanded tree.  A
memoization prototype behind `AGDA_DEADCODE_MEMO=1` is under
experiment in a dedicated copy of the Agda source; if it preserves
the kept sets and removes the blow-up, the finding and patch are
worth reporting to agda/agda.
