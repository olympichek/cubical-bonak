# Agda's dead-code interface pass on large telescopes

`main` worktree, Agda 2.8.0, 2026-08-20.  The subject is
`Agda.TypeChecking.DeadCode.eliminateDeadCode`
(`src/full/Agda/TypeChecking/DeadCode.hs` in the Agda source), the
pass that runs when an interface (`.agdai`) is written, and its cost
on the fused layer-2-coherence module of `Bonak/GpdLemmas.agda`.  It
is independent of the type-checking cost documented in
`CONV-COST.md`.

**Result: on stock Agda 2.8.0 the pass multiplies the file's build
several-fold — 3,525 s of a 4,298 s run on the single-telescope kit,
2,428 s of 2,936 s on the staged one — it is untouched by
source-level restructuring, and a StableName-memoized traversal was
built, verified correct, and measured SLOWER: the internal
representation is genuinely tree-sized, not a shared DAG.  Skipping
the pass is sound and is the practical local answer.**

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

Every definition inside a parameterized module is section-lifted, so
its internal type carries the whole telescope; the section telescopes
are roots; and every metavariable solved while checking the telescope
stores a type closed over its full context, all of which `goMeta`
traverses.  On a ~60-parameter dependent telescope whose late
parameters have enormous stated filler types, the reachable
representation is huge — and, decisively, it is *materialized*, not
shared: instrumented counters show ~89 K distinct
Term/Type/Telescope nodes referenced through ~33.5 M `Apply` spine
slots (fanout ~375), with sharing only at atomic subterms.  Spines
and meta context types are physically distinct, so any traversal
must visit each edge once; the cost is the honest size of the lifted
signature, super-linear in the number of parameters.

## Measurements

- Telescope-only prefix (60 parameters, trivial body): 76.9 s of the
  77.9 s run inside the `DeadCodeReachable` profiling bucket, typing
  0.3 s; ~90 s more per added filler parameter.  Scaling family on
  section prefixes: ~0 s → 3.5 s → 108 s → 2,825 s.
- Full kit file, stock behavior: `DeadCodeReachable` 3,524.9 s of
  4,298 s total (82%, 14.2 TB allocated), kept sets 138 definitions /
  2,108 metas; with the pass bypassed the same file is 762.9 s.
- The staged-telescope refactoring (`CONV-COST.md`), which halves
  typing, does not fix the pass: 2,428 s of a 2,936 s stock run —
  section-lifting reconstitutes the full concatenated telescope in
  the internal types whatever the module nesting.

The bypass (`AGDA_NO_DEADCODE=1` in the locally patched binary:
return all definitions, solved metas and closed display forms
unchanged) is always sound — the pass only prunes — at the price of
larger interfaces; downstream checking is unaffected.

## The memoization experiment (negative result)

A `StableName`-keyed node-visited memo (WHNF-forced keys, memo at
Term/Type/Telescope nodes, guarded by `AGDA_DEADCODE_MEMO=1`) was
implemented as a one-for-one mirror of the `NamesIn` fold and
verified correct: kept sets identical on every file measured both
ways, and the probe interface byte-identical across paths.  It
LOSES: a 99.74% hit rate still measures slower than stock on
completing probes (108 → 126 s), and on the full file the memoized
pass exceeded a 5,400 s cap that stock meets — per-edge
StableName/hashtable overhead plus stable-name-table scanning at
every minor GC outweigh the 8% of allocation the memo saves.  The
tree-vs-DAG hypothesis is refuted for this workload: there is no
sharing for a memo to exploit.

## Upstream

The root set is pinned by #6931/#7382, restructuring the source does
not help, and memoizing the traversal does not help.  What would
help is upstream reducing — or structurally sharing — what is stored
per solved metavariable and per section-lifted type, so that sharing
exists in the signature for any later pass to exploit.  The
upstream-worthy artifacts of this investigation are the pathology
data above and the section-telescope probe family as a regression
benchmark.
