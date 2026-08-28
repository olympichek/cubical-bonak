# Checking cost of the fused layer-2-coherence kit

`main` worktree, Agda 2.8.0, 2026-08-20.  The subject is the final
section of `Bonak/GpdLemmas.agda` — the anonymous module (~60
dependent parameters) whose public member `coh2Layer-cubeP` closes
`coh2-layer` — and where its checking time actually goes.  Interface
-pass overhead is a separate cost, documented in `DEADCODE-COST.md`;
all numbers here are with that pass bypassed.

**Result: the dominant cost is per-binding section overhead — every
definition inside the module is processed over the full telescope,
whose six filler parameters have enormous instantiated
`cohLayer-squareP` types — at ~5–9 s per private binding regardless
of the binding's own content.  Restructuring the section into a
staged telescope halves the file's checking time; restructuring the
pastings themselves does nothing.**

## Measurements

Baseline (full re-check of `GpdLemmas.agda`, locally patched binary,
interface pass bypassed): 766 s without profiling, 772 s under
`--profile=all`, 10.3 GB peak, 2.04 TB allocated.  Profile
breakdown: Typing ~405 s, Serialization ~158 s, Coverage ~112 s,
Positivity ~25 s.  Conversion statistics are small — 24k compares,
487 constraints — a few enormous problems, not many small ones.

Prefix bisection (the telescope restated with growing suffixes of the
private block) localizes the cost:

- the telescope alone checks in 9.7 s;
- the thirteen trivial slice one-liners (`aSK = subst T̃ κ' cS̃` and
  kin) cost ~103 s — ~8 s per binding, independent of content;
- the same ~5–9 s/binding rate holds across every group of bindings,
  including the junction cells and stated laterals;
- the cost is nonlocal (a strictly larger prefix once checked faster,
  from postponed-constraint wake-up order), and
  `--profile=definitions` attribution is unreliable here (~300 s
  lands in Miscellaneous).

An earlier binary-search scan that timed out inside the junction-cell
group had suggested the pasting composites themselves were the
hotspot; its own numbers — prefix times growing ~9 s per added
binding toward a fixed timeout ceiling — are in fact the same
per-binding rate, and the "heavy group" reading was an artifact of
the ceiling.

Two direct falsifications of the pasting-depth hypothesis:

- Flattening `junctionP`'s three-stage `∙r`/`∙rP` chains into a
  single `hfill`/`comp′` over `compPath-filler` (stated types kept
  verbatim) is performance-neutral on the full file (778 s).  The
  flat form is kept anyway, as the simpler definition.
- The conversion success-cache (`AGDA_CONV_CACHE=1`) is a wash on
  this file: 772 vs 768 s, 227 hits.

## The fix: staged telescope

The section is split into three nested anonymous modules that bind
parameters as late as possible — outer: the family/map/path
parameters through the base squares; middle: the four upper fillers;
inner: the remaining fillers, the premise pack and the base-pad data
— with each private binding placed in the innermost module whose
parameters it mentions.  Definitions then carry only the telescope
prefix they actually depend on.  The lifted parameter order of
`coh2Layer-cubeP` is unchanged, so the νGpd call site needs no edit.

Effect: full-file check 766 → ~400 s (2.0×); a prefix probe of the
restructured section drops 305–320 → 75 s (4.3×).  `νGpd.agda`
checks green throughout (113–130 s in the same environment).

The remaining floor is ~157 s of interface serialization (the stored
elaborated implicits of the pastings, untouched by any restructuring
tried) plus residual per-binding overhead; deeper nesting could shave
somewhat more.

The staging does NOT transfer to the stock interface pass: a
stock-behavior run of the staged file still spends 2,428 s in
`DeadCodeReachable` (section-lifting reconstitutes the full
telescope in the internal representation whatever the module
nesting) — see `DEADCODE-COST.md`.  Typing and the pass share the
telescope as driver but need separate remedies.

Experiment records: branch `conv-cost` (CONV-EXP-NOTES.md and the
probes `TelescopeOnly.agda`, `SectionPrefix.agda`,
`JunctionFlat.agda`).
