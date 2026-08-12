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
open import Bonak.LayerHexBridge

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

opaque
  unfolding mkCoh2FrameType

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

------------------------------------------------------------------------
-- Part 3b: the layer-level coherence hexagon (νGpd.v:755-844).
-- Statement family mkCoh2Layer* over a fixed previous coh2Frames; the
-- tower stages entering the statement are named so instance types stay
-- folded.  Level key (bounds of the ≤-proofs in the Rocq text):
--   rfO — bound suc k   (π₁C (c2DepsCohs dc2))
--   rfM — bound suc² k  (π₁C (mkDepsCohs (π₁C2 dc2)))
--   rfI — bound suc³ k  (π₁C of dcJ, νGpd.v:760's toDepsCohs (…).1)
--   rfJ — bound suc² k, the pair-level restriction (νGpd.v:811's
--         depsCohs' = toDepsCohs (mkCohFrames …), no final .1)
------------------------------------------------------------------------

module _ {p k : ℕ} (dc2 : DepsCohs2 (suc p) k)
  (eDC2 : DepsCohs2Extension (suc p) k dc2)
  (prevCoh2Frames : mkCoh2FrameTypes (mkExtraCohs (AddCoh2Dep dc2 eDC2))
                      (mkCohPaintings (AddCoh2Dep dc2 eDC2)))
  where

  private
    -- One storey down (Rocq's mkDepsCohs depsCohs2.(1)).
    dcT : DepsCohs (suc p) (suc k)
    dcT = mkDepsCohs (π₁C2 dc2)

    -- Two storeys down: νGpd.v:811's depsCohs'.
    dcJ : DepsCohs (suc p) (suc (suc k))
    dcJ = depsCohs (mkDepsRestr (π₁C dcT))
            (mkExtraDeps (AddCohDep dcT (mkExtraCohs (AddCoh2Dep dc2 eDC2))))
            (mkRestrPaintings (AddCohDep dcT (mkExtraCohs (AddCoh2Dep dc2 eDC2))))
            (mkCohFrames (AddCohDep dcT (mkExtraCohs (AddCoh2Dep dc2 eDC2)))
              (fst (mkCohPaintings (AddCoh2Dep dc2 eDC2)))
              (fst prevCoh2Frames))

    -- Three storeys down: νGpd.v:760's toDepsCohs (mkCohFrames …).1.
    dcI : DepsCohs p (suc (suc (suc k)))
    dcI = π₁C dcJ

    rfO = snd (mkRestrFramesC (π₁C (c2DepsCohs dc2)))
    rfM = snd (mkRestrFramesC (π₁C dcT))
    rfI = snd (mkRestrFramesC dcI)
    rfJ = snd (mkRestrFramesC dcJ)

    -- The three layer restrictions (mkRestrLayer at the three stages).
    RL0 = mkRestrLayer (cDeps (c2DepsCohs dc2)) (cExtraDeps (c2DepsCohs dc2))
            (snd (cRestrPaintings (c2DepsCohs dc2)))
            (mkRestrFramesC (π₁C (c2DepsCohs dc2)))
            (snd (cCohs (c2DepsCohs dc2)))
    RL1 = mkRestrLayer (cDeps dcT) (cExtraDeps dcT)
            (snd (cRestrPaintings dcT)) (mkRestrFramesC (π₁C dcT))
            (snd (cCohs dcT))
    RL2 = mkRestrLayer (cDeps dcJ) (cExtraDeps dcJ)
            (snd (cRestrPaintings dcJ)) (mkRestrFramesC (π₁C dcJ))
            (snd (cCohs dcJ))

    -- The two layer coherences entering the composites: the current
    -- storey's (CL1, the same instantiation mkCohFrames stores) and the
    -- previous storey's (CL2).
    CL1 = mkCohLayer (c2ExtraDepsCohs dc2) (snd (c2CohPaintings dc2))
            (mkCohFrames (AddCohDep (c2DepsCohs dc2) (c2ExtraDepsCohs dc2))
              (fst (c2CohPaintings dc2)) (fst (c2Coh2Frames dc2)))
            (snd (c2Coh2Frames dc2))
    CL2 = mkCohLayer (mkExtraCohs (AddCoh2Dep dc2 eDC2))
            (mkCohPainting (AddCoh2Dep dc2 eDC2))
            (mkCohFrames (AddCohDep (mkDepsCohs (π₁C2 dc2))
              (mkExtraCohs (AddCoh2Dep dc2 eDC2)))
              (fst (mkCohPaintings (AddCoh2Dep dc2 eDC2)))
              (fst prevCoh2Frames))
            (snd prevCoh2Frames)

    -- The layer families the composites live in.
    QL : GDom (mkFrame (π₁D (cDeps (c2DepsCohs dc2)))) → Set
    QL x = GDom (mkLayer p k (dFrames (cDeps (c2DepsCohs dc2)))
             (dPaintings (cDeps (c2DepsCohs dc2)))
             (fst (dRestrFrames (cDeps (c2DepsCohs dc2))))
             (snd (dRestrFrames (cDeps (c2DepsCohs dc2)))) x)
    PL : GDom (mkFrame (π₁D (cDeps dcT))) → Set
    PL x = GDom (mkLayer p (suc k) (dFrames (cDeps dcT))
             (dPaintings (cDeps dcT))
             (fst (dRestrFrames (cDeps dcT)))
             (snd (dRestrFrames (cDeps dcT))) x)

    -- The pointwise painting family: QL x ≐ (ζ : arity) → BL ζ x
    -- definitionally (mkLayer is a gΠ).
    BL : arity → GDom (mkFrame (π₁D (cDeps (c2DepsCohs dc2)))) → Set
    BL ζ x = GDom (snd (dPaintings (cDeps (c2DepsCohs dc2)))
               (snd (dRestrFrames (cDeps (c2DepsCohs dc2))) 0 tt ζ x))

    -- The two triple layer restrictions, named so the endpoint type,
    -- the bridge and the pointwise statement share one spelling.
    c2lTripleL : (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q)
      (s : ℕ) .(Hs : s ≤ r) (ε ω θ : arity)
      (d : GDom (mkFrame (π₁D (mkDepsRestr dcI))))
      (l : GDom (mkLayer p (suc (suc (suc k))) (mkFramesD (cDeps dcI))
            (mkPaintings (cExtraDeps dcI)) (fst (mkRestrFramesC dcI))
            (snd (mkRestrFramesC dcI)) d))
      → QL (rfO (suc q) Hq ε
             (rfM (suc r) (le-trans r q (suc k) Hr (le-up q k Hq)) ω
               (rfI (suc s)
                 (le-trans s r (suc (suc k)) Hs
                   (le-up r (suc k) (le-trans r q (suc k) Hr (le-up q k Hq))))
                 θ d)))
    c2lTripleL q Hq r Hr s Hs ε ω θ d l =
      let HrHq↑ = le-trans r q (suc k) Hr (le-up q k Hq)
          HsHrHq↑↑ = le-trans s r (suc (suc k)) Hs (le-up r (suc k) HrHq↑)
      in RL0 q Hq ε (rfM (suc r) HrHq↑ ω (rfI (suc s) HsHrHq↑↑ θ d))
           (RL1 r HrHq↑ ω (rfI (suc s) HsHrHq↑↑ θ d)
             (RL2 s HsHrHq↑↑ θ d l))

    c2lTripleR : (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q)
      (s : ℕ) .(Hs : s ≤ r) (ε ω θ : arity)
      (d : GDom (mkFrame (π₁D (mkDepsRestr dcI))))
      (l : GDom (mkLayer p (suc (suc (suc k))) (mkFramesD (cDeps dcI))
            (mkPaintings (cExtraDeps dcI)) (fst (mkRestrFramesC dcI))
            (snd (mkRestrFramesC dcI)) d))
      → QL (rfO (suc s) (le-trans s r k Hs (le-trans r q k Hr Hq)) θ
             (rfM (suc (suc r)) (le-trans r q k Hr Hq) ω
               (rfI (suc (suc (suc q))) Hq ε d)))
    c2lTripleR q Hq r Hr s Hs ε ω θ d l =
      let HrHq = le-trans r q k Hr Hq
      in RL0 s (le-trans s r k Hs HrHq) θ
           (rfM (suc (suc r)) HrHq ω (rfI (suc (suc (suc q))) Hq ε d))
           (RL1 (suc r) HrHq ω (rfI (suc (suc (suc q))) Hq ε d)
             (RL2 (suc (suc q)) Hq ε d l))

  -- The frame endpoint (νGpd.v:755): both triple restrictions, one
  -- storey up from mkCoh2PaintingFrameEndpointType.

  mkCoh2LayerFrameEndpointType :
    (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (s : ℕ) .(Hs : s ≤ r)
    (ε ω θ : arity)
    (d : GDom (mkFrame (π₁D (mkDepsRestr dcI))))
    → Set
  mkCoh2LayerFrameEndpointType q Hq r Hr s Hs ε ω θ d =
    let HrHq↑ = le-trans r q (suc k) Hr (le-up q k Hq)
        HrHq = le-trans r q k Hr Hq
    in
    rfO (suc q) Hq ε
      (rfM (suc r) HrHq↑ ω
        (rfI (suc s) (le-trans s r (suc (suc k)) Hs (le-up r (suc k) HrHq↑))
          θ d))
    ≡ rfO (suc s) (le-trans s r k Hs HrHq) θ
        (rfM (suc (suc r)) HrHq ω
          (rfI (suc (suc (suc q))) Hq ε d))

  -- The two triple layer restrictions the coh2Layer equates
  -- (νGpd.v:769), over a given frame endpoint.

  mkCoh2LayerEndpointType :
    (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (s : ℕ) .(Hs : s ≤ r)
    (ε ω θ : arity)
    (d : GDom (mkFrame (π₁D (mkDepsRestr dcI))))
    (l : GDom (mkLayer p (suc (suc (suc k))) (mkFramesD (cDeps dcI))
          (mkPaintings (cExtraDeps dcI)) (fst (mkRestrFramesC dcI))
          (snd (mkRestrFramesC dcI)) d))
    (coh2FrameEndpoint : mkCoh2LayerFrameEndpointType q Hq r Hr s Hs ε ω θ d)
    → Set
  mkCoh2LayerEndpointType q Hq r Hr s Hs ε ω θ d l coh2FrameEndpoint =
    subst QL coh2FrameEndpoint (c2lTripleL q Hq r Hr s Hs ε ω θ d l)
    ≡ c2lTripleR q Hq r Hr s Hs ε ω θ d l

  -- The layer coherence hexagon statement (νGpd.v:801), shaped exactly
  -- as Σ≡hex's HHu premise at mkCoh2Frames' call site.
  --
  -- NOTE (RUNG-2 BLOCKER, 2026-08-12): merely ELABORATING this
  -- statement at the top storey does not converge in reasonable time
  -- (killed at 2 min; an unpinned variant ran 64+ min) — the same wall
  -- the V2 (pathp) port hit on its top coh2Frame square.  Everything
  -- around it is fast (≤4 s): the private ladder, the named triples,
  -- mkCoh2Layer(Frame)EndpointType, and the abstract-κ2 bridge
  -- mkCoh2LayerFromPointwise below.  The cost is the concrete
  -- κ2 := snd prevCoh2Frames (suc q) … d subst (endpoint extraction
  -- converts the raw νGpdBase reduct against the ladder spellings) plus
  -- the six ⊙/sigT-map-eq factor types; opaque mkCoh2FrameType,
  -- raw-spelling CL2's prevCohFrames (which fixed the same wall one
  -- rung down, 2 min → 4 s), and pinning every ⊙/sigT-map-eq implicit
  -- were all applied and are kept below — they are not sufficient
  -- here.  Waiting on the conversion-cache Agda A/B.

{-
  opaque
    unfolding mkCoh2FrameType

    mkCoh2LayerType :
      (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (s : ℕ) .(Hs : s ≤ r)
      (ε ω θ : arity)
      (d : GDom (mkFrame (π₁D (mkDepsRestr dcI))))
      (l : GDom (mkLayer p (suc (suc (suc k))) (mkFramesD (cDeps dcI))
            (mkPaintings (cExtraDeps dcI)) (fst (mkRestrFramesC dcI))
            (snd (mkRestrFramesC dcI)) d))
      → Set
    mkCoh2LayerType q Hq r Hr s Hs ε ω θ d l =
      let HrHq↑ = le-trans r q (suc k) Hr (le-up q k Hq)
          HrHq = le-trans r q k Hr Hq
          HsHrHq = le-trans s r k Hs (le-trans r q k Hr Hq)
          b1 = snd (cCohs dcJ) (suc r) (le-trans r q (suc k) Hr (le-up q k Hq))
                 (suc s) Hs ω θ d
          b2 = snd (cCohs dcJ) (suc (suc q)) Hq (suc (suc r)) Hr ε ω d
          b3 = snd (cCohs dcJ) (suc (suc q)) Hq (suc s)
                 (le-up s q (le-trans s r q Hs Hr)) ε θ d
          c1 = snd (cCohs dcT) (suc q) Hq (suc s) (le-trans s r q Hs Hr) ε θ
                 (fst (rfJ (suc r) (le-trans r q (suc k) Hr (le-up q k Hq)) ω
                   (d , l)))
          c1' = snd (cCohs dcT) (suc q) Hq (suc r) Hr ε ω
                 (fst (rfJ s (le-up s (suc k) (le-up s k
                    (le-trans s r k Hs (le-trans r q k Hr Hq)))) θ (d , l)))
          c3' = snd (cCohs dcT) (suc r) (le-trans r q k Hr Hq) (suc s) Hs ω θ
                 (fst (rfJ (suc (suc q)) Hq ε (d , l)))
      in
      subst (mkCoh2LayerEndpointType q Hq r Hr s Hs ε ω θ d l)
        (snd prevCoh2Frames (suc q) Hq (suc r) Hr (suc s) Hs ε ω θ d)
        (_⊙_ {P = QL}
          {u = c2lTripleL q Hq r Hr s Hs ε ω θ d l}
          {w = c2lTripleR q Hq r Hr s Hs ε ω θ d l}
          {p = cong (λ x → rfO (suc q) Hq ε x) b1}
          (sigT-map-eq {P = PL} {Q = QL} {f = λ x → rfO (suc q) Hq ε x}
            (RL0 q Hq ε) {p = b1}
            (CL2 r HrHq↑ s Hs ω θ d l))
          {p' = c1 ∙ cong (λ x → rfO (suc s) HsHrHq θ x) b2}
          (_⊙_ {P = QL} {p = c1}
            (CL1 q Hq s (le-trans s r q Hs Hr) ε θ
              (fst (rfJ (suc r) HrHq↑ ω (d , l)))
              (snd (rfJ (suc r) HrHq↑ ω (d , l))))
            {p' = cong (λ x → rfO (suc s) HsHrHq θ x) b2}
            (sigT-map-eq {P = PL} {Q = QL} {f = λ x → rfO (suc s) HsHrHq θ x}
              (RL0 s HsHrHq θ) {p = b2}
              (CL2 (suc q) Hq (suc r) Hr ε ω d l))))
      ≡ _⊙_ {P = QL}
          {u = c2lTripleL q Hq r Hr s Hs ε ω θ d l}
          {w = c2lTripleR q Hq r Hr s Hs ε ω θ d l}
          {p = c1'}
          (CL1 q Hq r Hr ε ω
            (fst (rfJ s (le-up s (suc k) (le-up s k HsHrHq)) θ (d , l)))
            (snd (rfJ s (le-up s (suc k) (le-up s k HsHrHq)) θ (d , l))))
          {p' = cong (λ x → rfO (suc r) HrHq ω x) b3 ∙ c3'}
          (_⊙_ {P = QL} {p = cong (λ x → rfO (suc r) HrHq ω x) b3}
            (sigT-map-eq {P = PL} {Q = QL} {f = λ x → rfO (suc r) HrHq ω x}
              (RL0 r HrHq ω) {p = b3}
              (CL2 (suc q) Hq s (le-up s q (le-trans s r q Hs Hr)) ε θ d l))
            {p' = c3'}
            (CL1 r HrHq s Hs ω θ
              (fst (rfJ (suc (suc q)) Hq ε (d , l)))
              (snd (rfJ (suc (suc q)) Hq ε (d , l)))))

-}
  -- The pointwise face of the layer hexagon: what remains of a
  -- mkCoh2LayerType goal after the Π-layer bridge (νGpd.v:846's
  -- lmap2_hex_rew_eq step).  Named so goals stay one application.

  mkCoh2LayerPointwiseType :
    (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (s : ℕ) .(Hs : s ≤ r)
    (ε ω θ : arity)
    (d : GDom (mkFrame (π₁D (mkDepsRestr dcI))))
    (l : GDom (mkLayer p (suc (suc (suc k))) (mkFramesD (cDeps dcI))
          (mkPaintings (cExtraDeps dcI)) (fst (mkRestrFramesC dcI))
          (snd (mkRestrFramesC dcI)) d))
    {e1 e2 : mkCoh2LayerFrameEndpointType q Hq r Hr s Hs ε ω θ d}
    (κ2 : e1 ≡ e2)
    (u : mkCoh2LayerEndpointType q Hq r Hr s Hs ε ω θ d l e1)
    (v : mkCoh2LayerEndpointType q Hq r Hr s Hs ε ω θ d l e2)
    (ζ : arity) → Set
  mkCoh2LayerPointwiseType q Hq r Hr s Hs ε ω θ d l {e1} {e2} κ2 u v ζ =
    subst (λ e → subst (BL ζ) e (c2lTripleL q Hq r Hr s Hs ε ω θ d l ζ)
                 ≡ c2lTripleR q Hq r Hr s Hs ε ω θ d l ζ) κ2
      (Πcomp {B = BL} {e = e1}
        {f = c2lTripleL q Hq r Hr s Hs ε ω θ d l}
        {g = c2lTripleR q Hq r Hr s Hs ε ω θ d l} u ζ)
    ≡ Πcomp {B = BL} {e = e2}
        {f = c2lTripleL q Hq r Hr s Hs ε ω θ d l}
        {g = c2lTripleR q Hq r Hr s Hs ε ω θ d l} v ζ

  -- Everything of mkCoh2Layer except the pointwise content: the
  -- Π-layer hexagon bridge applied at QL ≐ (ζ : arity) → BL ζ.  The
  -- pointwise obligation is what GpdLemmas' rew-coh2Layer closes
  -- (statement-port only at the time of writing) after the
  -- Πcomp-commutation suite rewrites the components; see the resume
  -- block at the end of the file.

  mkCoh2LayerFromPointwise :
    (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (s : ℕ) .(Hs : s ≤ r)
    (ε ω θ : arity)
    (d : GDom (mkFrame (π₁D (mkDepsRestr dcI))))
    (l : GDom (mkLayer p (suc (suc (suc k))) (mkFramesD (cDeps dcI))
          (mkPaintings (cExtraDeps dcI)) (fst (mkRestrFramesC dcI))
          (snd (mkRestrFramesC dcI)) d))
    {e1 e2 : mkCoh2LayerFrameEndpointType q Hq r Hr s Hs ε ω θ d}
    (κ2 : e1 ≡ e2)
    (u : mkCoh2LayerEndpointType q Hq r Hr s Hs ε ω θ d l e1)
    (v : mkCoh2LayerEndpointType q Hq r Hr s Hs ε ω θ d l e2)
    (H : (ζ : arity)
         → mkCoh2LayerPointwiseType q Hq r Hr s Hs ε ω θ d l κ2 u v ζ)
    → subst (mkCoh2LayerEndpointType q Hq r Hr s Hs ε ω θ d l) κ2 u ≡ v
  mkCoh2LayerFromPointwise q Hq r Hr s Hs ε ω θ d l {e1} {e2} κ2 u v H =
    Π-hex-bridge {A' = arity} {B = BL} {e1 = e1} {e2 = e2} κ2
      {f = c2lTripleL q Hq r Hr s Hs ε ω θ d l}
      {g = c2lTripleR q Hq r Hr s Hs ε ω θ d l}
      u v H

------------------------------------------------------------------------
-- Part 3c: the DepsCohs3 storey (νGpd.v:942-982) — the compilable
-- skeleton.  mkDepsCohs2 (and everything after it) needs mkCoh2Frames,
-- whose Σ-snd is the mkCoh2Layer proof term; mkCoh2Layer is wired
-- through mkCoh2LayerFromPointwise above and is blocked only on the
-- pointwise engine (GpdLemmas' rew-coh2Layer, statement-port only).
-- See the resume block at the end of the file.
------------------------------------------------------------------------

record DepsCohs3 (p k : ℕ) : Set₁ where
  no-eta-equality; pattern
  constructor depsCohs3
  field
    c3DepsCohs2 : DepsCohs2 p k
    c3ExtraDepsCohs2 : DepsCohs2Extension p k c3DepsCohs2
    c3Coh2Paintings : mkCoh2PaintingTypes c3ExtraDepsCohs2
open DepsCohs3 public

toDepsCohs3 : {p k : ℕ} {dc2 : DepsCohs2 p k}
              {eDC2 : DepsCohs2Extension p k dc2}
              (coh2Paintings : mkCoh2PaintingTypes eDC2)
              → DepsCohs3 p k
toDepsCohs3 {p} {k} {dc2} {eDC2} coh2Paintings =
  depsCohs3 dc2 eDC2 coh2Paintings

π₁C3 : {p k : ℕ} → DepsCohs3 (suc p) k → DepsCohs3 p (suc k)
π₁C3 dc3 = depsCohs3 (π₁C2 (c3DepsCohs2 dc3))
                     (AddCoh2Dep (c3DepsCohs2 dc3) (c3ExtraDepsCohs2 dc3))
                     (fst (c3Coh2Paintings dc3))

------------------------------------------------------------------------
-- RESUME BLOCK (UNCHECKED TRANSCRIPTION) — νGpd.v:846-1178.
--
-- Everything below is blocked on closing mkCoh2Layer (νGpd.v:846),
-- which is blocked twice over: (1) its STATEMENT mkCoh2LayerType is
-- the rung-2 elaboration wall (see the NOTE above its commented-out
-- block); (2) its pointwise content needs GpdLemmas' rew-coh2Layer,
-- currently a statement-port (rew-coh2Layer-Type) without a proof.
-- The bridge step IS checked: mkCoh2LayerFromPointwise above reduces
-- any mkCoh2LayerType-shaped goal (abstract κ2/u/v) to the pointwise
-- family mkCoh2LayerPointwiseType.  What remains, per component ζ:
--   1. push Πcomp through the two composites of mkCoh2LayerType with
--      the (all proved) LayerHexBridge suite: Πcomp-⊙ for the ⊙'s,
--      Πcomp-sigT-map-eq for the sigT-map-eq (RL0 …) factors (their g
--      is pointwise: RL0 q Hq ε d′ l′ ζ = NA d′ ζ (l′ ζ) with
--      NA d′ ζ x = subst … (cohFrame q Hq 0 tt ε ζ d′)
--                    (rPtop q Hq ε (snd prevRF 0 tt ζ d′) x)),
--      Πcomp-Π-subst-ext for the mkCohLayer factors (they are
--      Π-subst-ext E (λ θ′ → rew-cohLayer33 …), so the ζ-component is
--      the stored rew-cohLayer33 instance);
--   2. close with GpdLemmas' rew-coh2Layer — the k-premises kP…kc5
--      instantiated at refl (our stored data are definitional
--      unfoldings), Hcoh2Painting := coh2Painting q Hq r Hr s Hs ε ω θ
--      (snd (mkRestrFramesC dcI) 0 tt ζ d) (l ζ), and Hcoh3Frame free
--      by GUIP: isGroupoidDom (mkFrame (cDeps (c2DepsCohs dc2))) _ _ _ _
--      (νGpd.v:918).  rew-coh2Layer is a statement-port only
--      (rew-coh2Layer-Type in GpdLemmas); its proof is the missing
--      piece.  The k=refl instantiation leaves refl-glue (lUnit-style)
--      to be absorbed when aligning with rew-coh2Layer-Type's
--      composites.
--
-- The remainder is a faithful transcription, kept as a comment so the
-- file stays axiom-free and fully checked.
{-

mkCoh2Layer : {p k : ℕ} (dc2 : DepsCohs2 (suc p) k)
  (eDC2 : DepsCohs2Extension (suc p) k dc2)
  (prevCoh2Frames : mkCoh2FrameTypes (mkExtraCohs (AddCoh2Dep dc2 eDC2))
                      (mkCohPaintings (AddCoh2Dep dc2 eDC2)))
  (coh2Painting : mkCoh2PaintingType dc2 eDC2)
  (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (s : ℕ) .(Hs : s ≤ r)
  (ε ω θ : arity) (d : _) (l : _)
  → mkCoh2LayerType dc2 eDC2 prevCoh2Frames q Hq r Hr s Hs ε ω θ d l
mkCoh2Layer dc2 eDC2 prevCoh2Frames coh2Painting q Hq r Hr s Hs ε ω θ d l =
  mkCoh2LayerFromPointwise dc2 eDC2 prevCoh2Frames q Hq r Hr s Hs ε ω θ d l
    (snd prevCoh2Frames (suc q) Hq (suc r) Hr (suc s) Hs ε ω θ d)
    ⟨LHS composite of mkCoh2LayerType⟩ ⟨RHS composite⟩
    (λ ζ → ⟨steps 1-2 of the header⟩)

-- νGpd.v:921 — the Σ-snd is Σ≡hex of the previous storey's hexagon and
-- THE mkCoh2Layer term (byte-identical to mkCoh2Painting's use below).
mkCoh2Frames : {p k : ℕ} {dc2 : DepsCohs2 p k}
  (eDC2 : DepsCohs2Extension p k dc2)
  (coh2Paintings : mkCoh2PaintingTypes eDC2)
  → mkCoh2FrameTypes (mkExtraCohs eDC2) (mkCohPaintings eDC2)
mkCoh2Frames {zero} eDC2 _ = tt , λ q Hq r Hr s Hs ε ω θ d → refl
mkCoh2Frames {suc p} {k} {dc2} eDC2 coh2Paintings =
  mkCoh2Frames (AddCoh2Dep dc2 eDC2) (fst coh2Paintings) ,
  λ q Hq r Hr s Hs ε ω θ (d , l) →
    Σ≡hex _ _ _ _ _ _   -- the three frame/layer restriction pairs
      (snd (mkCoh2Frames (AddCoh2Dep dc2 eDC2) (fst coh2Paintings))
        (suc q) Hq (suc r) Hr (suc s) Hs ε ω θ d)
      (mkCoh2Layer dc2 eDC2
        (mkCoh2Frames (AddCoh2Dep dc2 eDC2) (fst coh2Paintings))
        (snd coh2Paintings) q Hq r Hr s Hs ε ω θ d l)

-- νGpd.v:968
mkDepsCohs2 : {p k : ℕ} (dc3 : DepsCohs3 p k) → DepsCohs2 (suc p) k
mkDepsCohs2 dc3 =
  depsCohs2 (mkDepsCohs (c3DepsCohs2 dc3))
            (mkExtraCohs (c3ExtraDepsCohs2 dc3))
            (mkCohPaintings (c3ExtraDepsCohs2 dc3))
            (mkCoh2Frames (c3ExtraDepsCohs2 dc3) (c3Coh2Paintings dc3))

-- νGpd.v:976
data DepsCohs3Extension : (p k : ℕ) → DepsCohs3 p k → Set₁ where
  TopCoh3Dep : {p : ℕ} {dc3 : DepsCohs3 p 0}
    (E : GDom (mkFrame (mkDepsRestr (mkDepsCohs (mkDepsCohs2 dc3)))) → HGpd₀)
    → DepsCohs3Extension p 0 dc3
  AddCoh3Dep : {p k : ℕ} (dc3 : DepsCohs3 (suc p) k)
    → DepsCohs3Extension (suc p) k dc3
    → DepsCohs3Extension p (suc k) (π₁C3 dc3)

-- νGpd.v:993 (needs π₁C2 (mkDepsCohs2 dc3) ≐ mkDepsCohs2 (π₁C3 dc3),
-- which holds by the clause structure of mkCoh2Frames above)
mkExtraCohs2 : {p k : ℕ} {dc3 : DepsCohs3 p k}
  (eDC3 : DepsCohs3Extension p k dc3)
  → DepsCohs2Extension (suc p) k (mkDepsCohs2 dc3)
mkExtraCohs2 (TopCoh3Dep E) = TopCoh2Dep E
mkExtraCohs2 (AddCoh3Dep dc3 eDC3) =
  AddCoh2Dep (mkDepsCohs2 dc3) (mkExtraCohs2 eDC3)

-- νGpd.v:1003 — recursion on s (everything else re-generalized);
-- the s = 0 case needs the restr-0 analogue of the Πcomp suite
-- (Rocq's sigT_fst_lmap2_rew_eq: the ζ-component of a Σ≡dep through
-- the fst-projection layer map) plus GpdLemmas'
-- rew-coh2Painting-restr0 (statement-port only); the suc case is
-- Σ≡dep-hex (GpdLemmas, PROVED) of the SAME mkCoh2Layer instantiation
-- that mkCoh2Frames stored, and the recursive call at (d , l).
mkCoh2PaintingAux : (s : ℕ) {p k : ℕ} {dc3 : DepsCohs3 p k}
  (eDC3 : DepsCohs3Extension p k dc3)
  (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) .(Hs : s ≤ r)
  (ε ω θ : arity) (d : _) (c : _)
  → mkCoh2PaintingInstanceType (mkDepsCohs2 dc3) (mkExtraCohs2 eDC3)
      q Hq r Hr s Hs ε ω θ d c
mkCoh2PaintingAux zero eDC3 q Hq r Hr Hs ε ω θ d c =
  ⟨rew-coh2Painting-restr0 + Σ≡dep-fst bridge⟩
mkCoh2PaintingAux (suc s) eDC3 q Hq zero () ε ω θ d c
mkCoh2PaintingAux (suc s) eDC3 zero Hq (suc r) () ε ω θ d c
mkCoh2PaintingAux (suc s) (TopCoh3Dep E) (suc q) () (suc r) Hr Hs ε ω θ d c
mkCoh2PaintingAux (suc s) (AddCoh3Dep dc3 eDC3) (suc q) Hq (suc r) Hr Hs
  ε ω θ d (l , c) =
  Σ≡dep-hex ⟨A0/B/P0/R0/Pp/Rp and the three restriction triples,
             νGpd.v:1030-1070⟩
    (mkCoh2Layer (c3DepsCohs2 dc3) (c3ExtraDepsCohs2 dc3)
      (mkCoh2Frames (AddCoh2Dep (c3DepsCohs2 dc3) (c3ExtraDepsCohs2 dc3))
        (fst (c3Coh2Paintings dc3)))
      (snd (c3Coh2Paintings dc3)) q Hq r Hr s Hs ε ω θ d l)
    (mkCoh2PaintingAux s eDC3 q Hq r Hr Hs ε ω θ (d , l) c)

mkCoh2Painting : {p k : ℕ} {dc3 : DepsCohs3 p k}
  (eDC3 : DepsCohs3Extension p k dc3)
  → mkCoh2PaintingType (mkDepsCohs2 dc3) (mkExtraCohs2 eDC3)
mkCoh2Painting eDC3 q Hq r Hr s Hs ε ω θ d c =
  mkCoh2PaintingAux s eDC3 q Hq r Hr Hs ε ω θ d c

-- νGpd.v:1079
mkCoh2Paintings : {p k : ℕ} {dc3 : DepsCohs3 p k}
  (eDC3 : DepsCohs3Extension p k dc3)
  → mkCoh2PaintingTypes (mkExtraCohs2 eDC3)
mkCoh2Paintings {zero} eDC3 = tt , mkCoh2Painting eDC3
mkCoh2Paintings {suc p} {k} {dc3} eDC3 =
  mkCoh2Paintings (AddCoh3Dep dc3 eDC3) , mkCoh2Painting eDC3

-- νGpdData and the tower (νGpd.v:1091-1169), mirroring νSet.agda's
-- νSetData/mkνSetData/νSetStruct/νSetAt/νSetFrom one storey up.

record νGpdData (p : ℕ) : Set₁ where
  field
    gFrames : mkFrameTypes p 0
    gPaintings : mkPaintingTypes p 0 gFrames
    gRestrFrames : mkRestrFrameTypes p 0 gFrames gPaintings
    gRestrPaintings :
      (E : GDom (mkFrame (depsRestr gFrames gPaintings gRestrFrames))
           → HGpd₀)
      → mkRestrPaintingTypes
          {deps = depsRestr gFrames gPaintings gRestrFrames}
          (TopRestrDep E)
    gCohFrames :
      (E : GDom (mkFrame (depsRestr gFrames gPaintings gRestrFrames))
           → HGpd₀)
      → mkCohFrameTypes (TopRestrDep E) (gRestrPaintings E)
    gCohPaintings :
      (E : _) (E' : GDom (mkFrame (mkDepsRestr
              (depsCohs (depsRestr gFrames gPaintings gRestrFrames)
                (TopRestrDep E) (gRestrPaintings E) (gCohFrames E))))
            → HGpd₀)
      → mkCohPaintingTypes
          {dc = depsCohs (depsRestr gFrames gPaintings gRestrFrames)
                  (TopRestrDep E) (gRestrPaintings E) (gCohFrames E)}
          (TopCohDep E')
    gCoh2Frames :
      (E : _) (E' : _)
      → mkCoh2FrameTypes
          {dc = depsCohs (depsRestr gFrames gPaintings gRestrFrames)
                  (TopRestrDep E) (gRestrPaintings E) (gCohFrames E)}
          (TopCohDep E') (gCohPaintings E E')
    gCoh2Paintings :
      (E : _) (E' : _)
      (E'' : GDom (mkFrame (mkDepsRestr (mkDepsCohs
               (depsCohs2 (depsCohs _ (TopRestrDep E) (gRestrPaintings E)
                            (gCohFrames E))
                          (TopCohDep E') (gCohPaintings E E')
                          (gCoh2Frames E E'))))) → HGpd₀)
      → mkCoh2PaintingTypes
          {dc2 = depsCohs2 (depsCohs (depsRestr gFrames gPaintings
                             gRestrFrames)
                   (TopRestrDep E) (gRestrPaintings E) (gCohFrames E))
                   (TopCohDep E') (gCohPaintings E E') (gCoh2Frames E E')}
          (TopCoh2Dep E'')
open νGpdData public

mkνGpdData : {p : ℕ} (C : νGpdData p)
             (E : GDom (mkFrame (depsRestr (gFrames C) (gPaintings C)
                                           (gRestrFrames C))) → HGpd₀)
             → νGpdData (suc p)
mkνGpdData {p} C E = record
  { gFrames = mkFramesD deps0
  ; gPaintings = mkPaintings (TopRestrDep {deps = deps0} E)
  ; gRestrFrames = mkRestrFramesC dcE
  ; gRestrPaintings = λ E' → mkRestrPaintings {dc = dcE} (TopCohDep E')
  ; gCohFrames = λ E' → mkCohFrames {dc = dcE} (TopCohDep E')
                          (gCohPaintings C E E') (gCoh2Frames C E E')
  ; gCohPaintings = λ E' E'' → mkCohPaintings
      {dc2 = dc2E E'} (TopCoh2Dep E'')
  ; gCoh2Frames = λ E' E'' → mkCoh2Frames
      {dc2 = dc2E E'} (TopCoh2Dep E'') (gCoh2Paintings C E E' E'')
  ; gCoh2Paintings = λ E' E'' E''' → mkCoh2Paintings
      {dc3 = depsCohs3 (dc2E E') (TopCoh2Dep E'')
               (gCoh2Paintings C E E' E'')}
      (TopCoh3Dep E''')
  }
  where
  deps0 = depsRestr (gFrames C) (gPaintings C) (gRestrFrames C)
  dcE = depsCohs deps0 (TopRestrDep E) (gRestrPaintings C E)
                 (gCohFrames C E)
  dc2E = λ E' → depsCohs2 dcE (TopCohDep E') (gCohPaintings C E E')
                          (gCoh2Frames C E E')

record νGpdStruct (p : ℕ) : Set₂ where
  field
    prefix : Set₁
    struct : prefix → νGpdData p
open νGpdStruct public

mkGpdPrefix : (p : ℕ) (C : νGpdStruct p) → Set₁
mkGpdPrefix p C =
  Σ[ D ∈ prefix C ]
    (GDom (mkFrame (depsRestr (gFrames (struct C D))
                              (gPaintings (struct C D))
                              (gRestrFrames (struct C D)))) → HGpd₀)

mkνGpd0 : νGpdStruct 0
mkνGpd0 = record
  { prefix = Unit*
  ; struct = λ _ → record
      { gFrames = tt* ; gPaintings = tt* ; gRestrFrames = tt
      ; gRestrPaintings = λ E → tt
      ; gCohFrames = λ E → tt
      ; gCohPaintings = λ E E' → tt
      ; gCoh2Frames = λ E E' → tt
      ; gCoh2Paintings = λ E E' E'' → tt
      }
  }

mkνGpd : {p : ℕ} (C : νGpdStruct p) → νGpdStruct (suc p)
mkνGpd {p} C = record
  { prefix = mkGpdPrefix p C
  ; struct = λ D → mkνGpdData (struct C (fst D)) (snd D)
  }

νGpdAt : (n : ℕ) → νGpdStruct n
νGpdAt zero    = mkνGpd0
νGpdAt (suc n) = mkνGpd (νGpdAt n)

record νGpdFrom (n : ℕ) (X : prefix (νGpdAt n)) : Set₁ where
  coinductive
  field
    this : GDom (mkFrame (depsRestr (gFrames (struct (νGpdAt n) X))
                                    (gPaintings (struct (νGpdAt n) X))
                                    (gRestrFrames (struct (νGpdAt n) X))))
           → HGpd₀
    next : νGpdFrom (suc n) (X , this)
open νGpdFrom public

νGpds : Set₁
νGpds = νGpdFrom 0 tt*

-- Examples.agda gate (to be added there once the above compiles):
--   module SimplicialGpd = Bonak.νGpd ⊤
--   SemiSimplicial5g : Set₁
--   SemiSimplicial5g = SimplicialGpd.prefix (SimplicialGpd.νGpdAt 5)

-}

