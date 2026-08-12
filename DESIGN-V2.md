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
