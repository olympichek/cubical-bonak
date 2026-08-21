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
source-level restructuring, and two traversal-side redesigns
(StableName memoization; serializer-style interning) were built,
verified correct, and measured at parity or worse: the internal
representation is genuinely tree-sized, and ~85% of the pass is
simply forcing and visiting it.  The pathology has a precise seat —
the judgement types of solved metavariables, walked by `goMeta` but
discarded before serialization whenever `--save-metas` is off — and
skipping them collapses the pass 164× (2,726 s → 16.6 s) with a
byte-identical interface.  That, not a cleverer walk, is the fix.**

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

## The serializer-fusion experiment (negative result, decisive clue)

The serializer's small profile bucket (~146–166 s on the same
module) suggested computing reachability with its interning
discipline.  Implemented (`AGDA_DEADCODE_FUSE=1`: worklist over
definitions, one interning walk mirroring `NamesIn`), verified
correct (kept sets identical; `GpdLemmas.agdai` byte-identical by
md5 across stock/fuse/control; νGpd checks green against the fused
interface), and measured at PARITY: 2,756 s vs stock's 2,726 s,
despite a 99.87% structural hit rate (139.8 M hits).  Two reasons,
both structural:

- the serializer has no descent-skipping memo for structure —
  `EmbPrj Term/Type` encodes children before interning the node, so
  "hits don't re-descend" is unimplementable for any bottom-up key;
  only shallow-keyed QName/Name lookups skip descent; and
- the serializer never walks the expensive data at all: with
  `--save-metas` off, `instantiateFull` on the `Interface` drops the
  whole meta store before serialization, so its bucket covers
  definitions only.

A forcing-only control (`AGDA_DEADCODE_FORCE=1`, 2,306 s) bounds all
traversal discipline at ≤15% of the pass: ~85% is forcing and
visiting 3.89 × 10⁹ elim-edges of tree-sized input (~0.6 µs each).
No traversal redesign can win; the input has to shrink.

The encode-first variant (sweep a compact node table after
serialization instead of the syntax tree before it) was also built
and refuted at stress scale: the compact graph is real (~3–6 × 10⁵
nodes, swept in ~1 s) but encoding the unpruned meta store is the
same bottom-up descent — it blew a 5,400 s cap with a projected
>10,000 s full encode — because the serializer's structural keys
cannot skip descent and its usual ~150 s bucket never covered the
metas at all.  The same experiment independently replicated the
judgement-type fix below: 15.9 s, byte-identical interface.

## The fix: stop walking dropped meta judgement types

`goMeta` traverses, for every solved metavariable, its instantiation
AND its judgement type (`jMetaType`) — and the judgement types,
context-closed over the giant telescope, are the bulk of the input.
But whenever `--save-metas` is off, the meta store is discarded
before serialization anyway: nothing reachable only through a
judgement type can occur in the written interface.  Skipping
`jMetaType` in `goMeta` (prototype guard `AGDA_DEADCODE_NOJTYPE=1`;
the real condition should be `optSaveMetas`) collapses the pass from
2,726 s to 16.6 s — 164×, bringing the module's total from ~3,200 s
to 428 s — with the produced interface BYTE-IDENTICAL to stock's
(the 74 additional metas stock keeps are dropped downstream
regardless; definitions unchanged at 141).

## Upstream

The root set is pinned by #6931/#7382, source restructuring does not
help, and no traversal discipline helps.  The upstreamable change is
the `jMetaType` skip conditioned on `optSaveMetas` (with #7382's
`--save-metas` regression as the reason for the condition), backed
by the pathology data above and the section-telescope probe family
as a regression benchmark.  With `--save-metas` on, the judgement
types are genuinely needed and the blow-up returns; reducing what a
solved meta stores remains the only fix for that configuration.

Measurement caveat: the fuse-experiment runs were taken with a
sibling experiment sharing the machine (≥40 GB free throughout;
~±15% cross-run bucket variance), which does not affect the orders
of magnitude above.
