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

------------------------------------------------------------------------
-- Part 3: the level-3 coherence machinery (νGpd.v:653-1130).
-- The endpoint-type ladder keeps every instance type a named
-- application (νGpd.v:692's goal-folding, doubly important since the
-- no-eta switch makes syntactic equality the fast path).
------------------------------------------------------------------------

open import Bonak.GpdLemmas

-- The painting family the coh2Painting statement quantifies over
-- (νGpd.v:653): the painting of the (suc p, k)-tower two π₁'s down.

mkCoh2PaintingSourcePainting : {p k : ℕ}
  (dc2 : DepsCohs2 (suc p) k)
  (eDC2 : DepsCohs2Extension (suc p) k dc2)
  (d : GDom (mkFrame (π₁D (mkDepsRestr (π₁C (π₁C (mkDepsCohs dc2)))))))
  → HGpd₀
mkCoh2PaintingSourcePainting dc2 eDC2 d =
  mkPainting
    (AddRestrDep (mkDepsRestr (π₁C (π₁C (mkDepsCohs dc2))))
      (mkExtraDeps (AddCohDep (π₁C (mkDepsCohs dc2))
        (AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2)))))
    d

-- The frame endpoint (νGpd.v:661): both triple restrictions of d.

mkCoh2PaintingFrameEndpointType : {p k : ℕ}
  (dc2 : DepsCohs2 (suc p) k)
  (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (s : ℕ) .(Hs : s ≤ r)
  (ε ω θ : arity)
  (d : GDom (mkFrame (π₁D (mkDepsRestr (π₁C (π₁C (mkDepsCohs dc2)))))))
  → Set
mkCoh2PaintingFrameEndpointType {p} {k} dc2 q Hq r Hr s Hs ε ω θ d =
  snd (dRestrFrames (cDeps (c2DepsCohs dc2))) q Hq ε
    (snd (mkRestrFramesC (π₁C (c2DepsCohs dc2)))
      r (le-trans r q (suc k) Hr (le-up q k Hq)) ω
      (snd (mkRestrFramesC (π₁C (π₁C (mkDepsCohs dc2)))) s
        (le-trans s r (suc (suc k)) Hs
          (le-up r (suc k) (le-trans r q (suc k) Hr (le-up q k Hq)))) θ d))
  ≡ snd (dRestrFrames (cDeps (c2DepsCohs dc2))) s
      (le-trans s r k Hs (le-trans r q k Hr Hq)) θ
      (snd (mkRestrFramesC (π₁C (c2DepsCohs dc2)))
        (suc r) (le-trans r q k Hr Hq) ω
        (snd (mkRestrFramesC (π₁C (π₁C (mkDepsCohs dc2))))
          (suc (suc q)) Hq ε d))

-- The two triple-restricted paintings the coh2Painting equates
-- (νGpd.v:672), over a given frame endpoint.

mkCoh2PaintingEndpointType : {p k : ℕ}
  (dc2 : DepsCohs2 (suc p) k)
  (eDC2 : DepsCohs2Extension (suc p) k dc2)
  (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (s : ℕ) .(Hs : s ≤ r)
  (ε ω θ : arity)
  (d : GDom (mkFrame (π₁D (mkDepsRestr (π₁C (π₁C (mkDepsCohs dc2)))))))
  (c : GDom (mkCoh2PaintingSourcePainting dc2 eDC2 d))
  (coh2FrameEndpoint :
     mkCoh2PaintingFrameEndpointType dc2 q Hq r Hr s Hs ε ω θ d)
  → Set
mkCoh2PaintingEndpointType {p} {k} dc2 eDC2 q Hq r Hr s Hs ε ω θ d c
  coh2FrameEndpoint =
  let rP1 = mkRestrPainting (AddCohDep (c2DepsCohs dc2)
              (c2ExtraDepsCohs dc2))
      rP2 = mkRestrPainting (AddCohDep (π₁C (mkDepsCohs dc2))
              (AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2)))
      HsHrHq = le-trans s r (suc (suc k)) Hs
                 (le-up r (suc k) (le-trans r q (suc k) Hr (le-up q k Hq)))
  in
  subst (λ x → GDom (snd (dPaintings (cDeps (c2DepsCohs dc2))) x))
    coh2FrameEndpoint
    (snd (cRestrPaintings (c2DepsCohs dc2)) q Hq ε
      (snd (mkRestrFramesC (π₁C (c2DepsCohs dc2)))
        r (le-trans r q (suc k) Hr (le-up q k Hq)) ω
        (snd (mkRestrFramesC (π₁C (π₁C (mkDepsCohs dc2)))) s HsHrHq θ d))
      (rP1 r (le-trans r q (suc k) Hr (le-up q k Hq)) ω
        (snd (mkRestrFramesC (π₁C (π₁C (mkDepsCohs dc2)))) s HsHrHq θ d)
        (rP2 s HsHrHq θ d c)))
  ≡ snd (cRestrPaintings (c2DepsCohs dc2)) s
      (le-trans s r k Hs (le-trans r q k Hr Hq)) θ
      (snd (mkRestrFramesC (π₁C (c2DepsCohs dc2)))
        (suc r) (le-trans r q k Hr Hq) ω
        (snd (mkRestrFramesC (π₁C (π₁C (mkDepsCohs dc2))))
          (suc (suc q)) Hq ε d))
      (rP1 (suc r) (le-trans r q k Hr Hq) ω
        (snd (mkRestrFramesC (π₁C (π₁C (mkDepsCohs dc2))))
          (suc (suc q)) Hq ε d)
        (rP2 (suc (suc q)) Hq ε d c))

-- The coh2Painting instance statement (νGpd.v:697): a named definition
-- so goals stay one application (νGpd.v:692's folding note).

mkCoh2PaintingInstanceType : {p k : ℕ}
  (dc2 : DepsCohs2 (suc p) k)
  (eDC2 : DepsCohs2Extension (suc p) k dc2)
  (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (s : ℕ) .(Hs : s ≤ r)
  (ε ω θ : arity)
  (d : GDom (mkFrame (π₁D (mkDepsRestr (π₁C (π₁C (mkDepsCohs dc2)))))))
  (c : GDom (mkCoh2PaintingSourcePainting dc2 eDC2 d))
  → Set
mkCoh2PaintingInstanceType {p} {k} dc2 eDC2 q Hq r Hr s Hs ε ω θ d c =
  let rP2 = mkRestrPainting (AddCohDep (π₁C (mkDepsCohs dc2))
              (AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2)))
      rF2 = snd (mkRestrFramesC (π₁C (π₁C (mkDepsCohs dc2))))
      HrHq↑ = le-trans r q (suc k) Hr (le-up q k Hq)
      P₀ = λ x → GDom (snd (dPaintings (cDeps (c2DepsCohs dc2))) x)
  in
  subst (mkCoh2PaintingEndpointType dc2 eDC2 q Hq r Hr s Hs ε ω θ d c)
    (snd (c2Coh2Frames dc2) q Hq r Hr s Hs ε ω θ d)
    (_⊙_ {P = P₀}
      (sigT-map-eq {P = λ x → GDom (mkPainting
             (cExtraDeps (π₁C (c2DepsCohs dc2))) x)} {Q = P₀}
        (snd (cRestrPaintings (c2DepsCohs dc2)) q Hq ε)
        (mkCohPainting (AddCoh2Dep dc2 eDC2)
          r HrHq↑ s Hs ω θ d c))
      (_⊙_ {P = P₀}
        (snd (c2CohPaintings dc2) q Hq s (le-trans s r q Hs Hr) ε θ
          (rF2 (suc r) HrHq↑ ω d)
          (rP2 (suc r) HrHq↑ ω d c))
        (sigT-map-eq {P = λ x → GDom (mkPainting
               (cExtraDeps (π₁C (c2DepsCohs dc2))) x)} {Q = P₀}
          (snd (cRestrPaintings (c2DepsCohs dc2)) s
            (le-trans s r k Hs (le-trans r q k Hr Hq)) θ)
          (mkCohPainting (AddCoh2Dep dc2 eDC2)
            (suc q) Hq (suc r) Hr ε ω d c))))
  ≡ _⊙_ {P = P₀}
      (snd (c2CohPaintings dc2) q Hq r Hr ε ω
        (rF2 s (le-up s (suc k) (le-up s k
          (le-trans s r k Hs (le-trans r q k Hr Hq)))) θ d)
        (rP2 s (le-up s (suc k) (le-up s k
          (le-trans s r k Hs (le-trans r q k Hr Hq)))) θ d c))
      (_⊙_ {P = P₀}
        (sigT-map-eq {P = λ x → GDom (mkPainting
               (cExtraDeps (π₁C (c2DepsCohs dc2))) x)} {Q = P₀}
          (snd (cRestrPaintings (c2DepsCohs dc2)) r
            (le-trans r q k Hr Hq) ω)
          (mkCohPainting (AddCoh2Dep dc2 eDC2)
            (suc q) Hq s (le-up s q (le-trans s r q Hs Hr)) ε θ d c))
        (snd (c2CohPaintings dc2) r (le-trans r q k Hr Hq) s Hs ω θ
          (rF2 (suc (suc q)) Hq ε d)
          (rP2 (suc (suc q)) Hq ε d c)))

mkCoh2PaintingType : {p k : ℕ}
  (dc2 : DepsCohs2 (suc p) k)
  (eDC2 : DepsCohs2Extension (suc p) k dc2) → Set
mkCoh2PaintingType {p} {k} dc2 eDC2 =
  (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (s : ℕ) .(Hs : s ≤ r)
  (ε ω θ : arity)
  (d : GDom (mkFrame (π₁D (mkDepsRestr (π₁C (π₁C (mkDepsCohs dc2)))))))
  (c : GDom (mkCoh2PaintingSourcePainting dc2 eDC2 d))
  → mkCoh2PaintingInstanceType dc2 eDC2 q Hq r Hr s Hs ε ω θ d c

mkCoh2PaintingTypes : {p k : ℕ} {dc2 : DepsCohs2 p k}
  (eDC2 : DepsCohs2Extension p k dc2) → Set
mkCoh2PaintingTypes {zero} _ = ⊤
mkCoh2PaintingTypes {suc p} {k} {dc2} eDC2 =
  Σ[ _ ∈ mkCoh2PaintingTypes (AddCoh2Dep dc2 eDC2) ]
    mkCoh2PaintingType dc2 eDC2
