# V2 — PathP-native νSet/νGpd (branch `pathp`)

Coherences stated as (nested) `PathP`, in the shape Astra's
permutahedron coherences predict (notes/PathP-self-similarity.md §6):
lower proofs enter *through the family, applied to interval variables*.
Diverges from V1 (`main`) as follows; everything else (frames tower,
Π-layers, irrelevant ≤, Deps records) is kept.

## Statement changes

- `mkCohPaintingType`: no subst —
  `PathP (λ i → El (paintings (cohFrame-instance i))) (restrP…) (restrP…)`.
- `mkCohLayer`'s statement: a PathP of layers. Layers are Π, and a
  PathP of functions IS a function into PathPs *definitionally* —
  no `Π-subst-ext`, no funExt bridge, no toPathP.
- `mkCoh2FrameType` (νGpd): a `SquareP` — PathP between the two
  composite cohFrame paths — with the s-family applied to interval
  variables, textually matching Astra's `(Perm X µ)₃` shape.
- `mkRestrLayer` still transports values (transp along the PathP
  family line — same operation, no statement-level subst).

## Proof changes

- Σ-assembly (`mkCohFrames`, `mkCohPainting`): definitional PathP
  pairing `λ i → (hu i , hv i)` — Σ≡/Σ≡dep vanish.
- The fused `rew-cohLayer33` chain is replaced by square filling:
  at νSet level the frame-side square comes from `isSet→Square`
  (any parallel paths in an HSet bound a square); at νGpd level from
  the stored coh2 SquareP applied to (i, j).
- Composite SIDES still exist (the caveat of §6: hcomp is weakly
  associative) — where V1 chained substComposite, V2 uses
  compPath-filler-style hfill squares.

## Gates

1. νSet tower typechecks; SemiSimplicial4 normal form measured
   against V1's (~30KB with transp residue) — expect fewer stuck
   transp (statements never introduce subst).
2. Coherence statements printed side-by-side with Astra's paper
   shapes for the record.
3. Timing vs V1 (same machine, same Agda).

## νGpd part 3 addendum (2026-08-12)

Principle: every V1 rew-* megalemma is replaced by direct cube
assembly; propositional truncation enters at EXACTLY ONE site,
mirroring Rocq's single GUIP use (νGpd.v:918, the final cell inside
mkCoh2Layer's proof — everything else is stored data or hcomp).

1. **Kit** (RewLemmas.agda here): `SquareP` over a binary family;
   `isGroupoid→SquareP` (fill a SquareP with prescribed four sides
   over a prescribed base square, fibers groupoids — the 2-level
   analogue of isSet→Square, via isGroupoid→isSetPathP); a
   `compPathP`-filler if the assembly needs composite sides.
2. **DepsCohs2 storey**: records/extensions port 1:1 from V1
   (main@d035099 νGpd.agda:1-260 — shapes are statement-agnostic);
   mkCohPainting keeps V2 νSet's PathP r-recursion (no Σ≡dep; base
   case is a degenerate/connection square as in V2 νSet).
3. **mkCoh2PaintingType**: a `SquareP (λ i j → GDom (… (coh2Frame
   -instance i j)))` whose four sides are cohPainting PathPs — no
   Source/Endpoint/Instance subst-ladder at all (V1's νGpd.v:653-754
   machinery exists only to name transport endpoints; PathP names
   them by the family). This is the statement to print for the Astra
   comparison (gate 2): the s-family applied to interval variables.
4. **mkCoh2Layer**: layers are Π, so a SquareP of layers is pointwise
   a function into SquarePs definitionally. The proof is one cube:
   faces = the stored coh2Painting square (this storey's premise) +
   the stored coh2Frame squares (previous storey) + cohPainting
   sides; closed by the single isGroupoid→SquareP filling. This
   REPLACES rew-coh2Layer (~40 premises) + permutahedral-coherence +
   the κ-conjugation cascade entirely. Level arithmetic for the
   three storeys of restrictions: copy V1's dcT/dcJ/dcI ladder
   (main@9fc4c5b νGpd.agda part 3b header — bounds suc k / suc² k /
   suc³ k).
5. **mkCoh2Frames**: same interleaved-mutual shape as parts 1-2's
   mkCoh2FrameTypes⋈mkCohFrames, one level up
   (mkCoh3FrameTypes-analogue is NOT stored — νGpd stops at coh2;
   the mutual is coh2FrameTypes⋈... consult νGpd.v:921-1000).
6. **DepsCohs3 storey + mkCoh2Painting (s-recursion)**: statement is
   the SquareP of (3); the s-recursion's base case (restr0) should be
   a connection/filler square, replacing rew-coh2Painting-restr0.
7. **νGpdData, tower, coinductive, SemiSimplicial5 gate** as V1.

Expected deliverable beyond parity: a census of what vanished —
V1 needs {rew-coh2Layer, rew-coh2Painting-restr0, permutahedral-
coherence, Σ≡hex, Σ≡dep-hex, the ⊙-computation suite}; V2 should
need {isGroupoid→SquareP, ≤2 fillers}. That count is the measured
answer to "how much of the coherence bureaucracy is Id-encoding
artifact".
