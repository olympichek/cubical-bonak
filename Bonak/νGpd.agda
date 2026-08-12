------------------------------------------------------------------------
-- Bonak.νGpd — V1 direct mirror of Rocq theories/νSet/νGpd.v,
-- continued: the DepsCohs2/DepsCohs3 storeys and the level-3
-- coherence proofs. Tower base in Bonak.νGpdBase (split for interface
-- caching: this file carries the conversion-heavy definitions).
------------------------------------------------------------------------

module Bonak.νGpd (arity : Set) where

open import Bonak.Prelude
open import Bonak.LeProp
open import Bonak.RewLemmas
open import Bonak.νGpdBase arity public

-- The DepsCohs2 class (νGpd: carries cohPaintings AND coh2Frames) ------------

record DepsCohs2 (p k : ℕ) : Set₁ where
  no-eta-equality; pattern
  constructor depsCohs2
  field
    c2DepsCohs : DepsCohs p k
    c2ExtraDepsCohs : DepsCohsExtension p k c2DepsCohs
    c2CohPaintings : mkCohPaintingTypes c2ExtraDepsCohs
    c2Coh2Frames : mkCoh2FrameTypes c2ExtraDepsCohs c2CohPaintings
open DepsCohs2 public

toDepsCohs2 : {p k : ℕ} {dc : DepsCohs p k}
              {eDC : DepsCohsExtension p k dc}
              {cohPaintings : mkCohPaintingTypes eDC}
              (coh2Frames : mkCoh2FrameTypes eDC cohPaintings)
              → DepsCohs2 p k
toDepsCohs2 {p} {k} {dc} {eDC} {cohPaintings} coh2Frames =
  depsCohs2 dc eDC cohPaintings coh2Frames

π₁C2 : {p k : ℕ} → DepsCohs2 (suc p) k → DepsCohs2 p (suc k)
π₁C2 dc2 = depsCohs2 (π₁C (c2DepsCohs dc2))
                     (AddCohDep (c2DepsCohs dc2) (c2ExtraDepsCohs dc2))
                     (fst (c2CohPaintings dc2))
                     (fst (c2Coh2Frames dc2))

mkCohFramesC : {p k : ℕ} (dc2 : DepsCohs2 p k)
               → mkCohFrameTypes (mkExtraDeps (c2ExtraDepsCohs dc2))
                   (mkRestrPaintings (c2ExtraDepsCohs dc2))
mkCohFramesC dc2 = mkCohFrames (c2ExtraDepsCohs dc2)
                     (c2CohPaintings dc2) (c2Coh2Frames dc2)

mkDepsCohs : {p k : ℕ} (dc2 : DepsCohs2 p k) → DepsCohs (suc p) k
mkDepsCohs dc2 =
  depsCohs (mkDepsRestr (c2DepsCohs dc2))
           (mkExtraDeps (c2ExtraDepsCohs dc2))
           (mkRestrPaintings (c2ExtraDepsCohs dc2))
           (mkCohFramesC dc2)

data DepsCohs2Extension : (p k : ℕ) → DepsCohs2 p k → Set₁ where
  TopCoh2Dep : {p : ℕ} {dc2 : DepsCohs2 p 0}
    (E : GDom (mkFrame (mkDepsRestr (mkDepsCohs dc2))) → HGpd₀)
    → DepsCohs2Extension p 0 dc2
  AddCoh2Dep : {p k : ℕ} (dc2 : DepsCohs2 (suc p) k)
    → DepsCohs2Extension (suc p) k dc2
    → DepsCohs2Extension p (suc k) (π₁C2 dc2)

mkExtraCohs : {p k : ℕ} {dc2 : DepsCohs2 p k}
              (eDC2 : DepsCohs2Extension p k dc2)
              → DepsCohsExtension (suc p) k (mkDepsCohs dc2)
mkExtraCohs (TopCoh2Dep E) = TopCohDep E
mkExtraCohs (AddCoh2Dep dc2 eDC2) =
  AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2)

-- The painting coherence (νGpd's mkCohPainting): recursion on r; the
-- Σ-components are the same mkCohLayer proof term mkCohFrames stored.

mkCohPainting : {p k : ℕ} {dc2 : DepsCohs2 p k}
                (eDC2 : DepsCohs2Extension p k dc2)
                → mkCohPaintingType (mkExtraCohs eDC2)
mkCohPainting eDC2 q Hq zero Hr ε ω d (l , c) = refl
mkCohPainting eDC2 zero Hq (suc r) () ε ω d c
mkCohPainting (TopCoh2Dep E) (suc q) () (suc r) Hr ε ω d c
mkCohPainting (AddCoh2Dep dc2 eDC2) (suc q) Hq (suc r) Hr ε ω d (l , c) =
  Σ≡dep {P = λ x → GDom (mkLayer _ _
                (dFrames (cDeps (c2DepsCohs dc2)))
                (dPaintings (cDeps (c2DepsCohs dc2)))
                (fst (dRestrFrames (cDeps (c2DepsCohs dc2))))
                (snd (dRestrFrames (cDeps (c2DepsCohs dc2)))) x)}
        {Q = λ z → GDom (mkPainting (cExtraDeps (c2DepsCohs dc2)) z)}
        (snd prev (suc q) Hq (suc r) Hr ε ω d)
        (mkCohLayer (c2ExtraDepsCohs dc2) (snd (c2CohPaintings dc2))
          prev (snd (c2Coh2Frames dc2)) q Hq r Hr ε ω d l)
        (mkCohPainting eDC2 q Hq r Hr ε ω (d , l) c)
  where
  prev = mkCohFrames (AddCohDep (c2DepsCohs dc2) (c2ExtraDepsCohs dc2))
                     (fst (c2CohPaintings dc2)) (fst (c2Coh2Frames dc2))

mkCohPaintingsPrefix : {p k : ℕ} {dc2 : DepsCohs2 p k}
  (eDC2 : DepsCohs2Extension p k dc2)
  → mkCohPaintingTypes (AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2))
mkCohPaintingsPrefix {zero} _ = tt
mkCohPaintingsPrefix {suc p} {k} {dc2} eDC2 =
  mkCohPaintingsPrefix (AddCoh2Dep dc2 eDC2) ,
  mkCohPainting (AddCoh2Dep dc2 eDC2)

mkCohPaintings : {p k : ℕ} {dc2 : DepsCohs2 p k}
  (eDC2 : DepsCohs2Extension p k dc2)
  → mkCohPaintingTypes (mkExtraCohs eDC2)
mkCohPaintings eDC2 = mkCohPaintingsPrefix eDC2 , mkCohPainting eDC2
