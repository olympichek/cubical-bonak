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

{-
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
            (cCohs dcJ)
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
    let HrHq↑ = le-trans r q (suc k) Hr (le-up q k Hq)
        HrHq = le-trans r q k Hr Hq
        HsHrHq↑↑ = le-trans s r (suc (suc k)) Hs
                     (le-up r (suc k) (le-trans r q (suc k) Hr (le-up q k Hq)))
    in
    subst QL coh2FrameEndpoint
      (RL0 q Hq ε
        (rfM (suc r) HrHq↑ ω (rfI (suc s) HsHrHq↑↑ θ d))
        (RL1 r HrHq↑ ω (rfI (suc s) HsHrHq↑↑ θ d)
          (RL2 s HsHrHq↑↑ θ d l)))
    ≡ RL0 s (le-trans s r k Hs HrHq) θ
        (rfM (suc (suc r)) HrHq ω (rfI (suc (suc (suc q))) Hq ε d))
        (RL1 (suc r) HrHq ω (rfI (suc (suc (suc q))) Hq ε d)
          (RL2 (suc (suc q)) Hq ε d l))

  -- The layer coherence hexagon statement (νGpd.v:801), shaped exactly
  -- as Σ≡hex's HHu premise at mkCoh2Frames' call site.

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
    in
    subst (mkCoh2LayerEndpointType q Hq r Hr s Hs ε ω θ d l)
      (snd prevCoh2Frames (suc q) Hq (suc r) Hr (suc s) Hs ε ω θ d)
      (_⊙_ {P = QL}
        (sigT-map-eq {P = PL} {Q = QL}
          (RL0 q Hq ε)
          (CL2 r HrHq↑ s Hs ω θ d l))
        (_⊙_ {P = QL}
          (CL1 q Hq s (le-trans s r q Hs Hr) ε θ
            (fst (rfJ (suc r) HrHq↑ ω (d , l)))
            (snd (rfJ (suc r) HrHq↑ ω (d , l))))
          (sigT-map-eq {P = PL} {Q = QL}
            (RL0 s HsHrHq θ)
            (CL2 (suc q) Hq (suc r) Hr ε ω d l))))
    ≡ _⊙_ {P = QL}
        (CL1 q Hq r Hr ε ω
          (fst (rfJ s (le-up s (suc k) (le-up s k HsHrHq)) θ (d , l)))
          (snd (rfJ s (le-up s (suc k) (le-up s k HsHrHq)) θ (d , l))))
        (_⊙_ {P = QL}
          (sigT-map-eq {P = PL} {Q = QL}
            (RL0 r HrHq ω)
            (CL2 (suc q) Hq s (le-up s q (le-trans s r q Hs Hr)) ε θ d l))
          (CL1 r HrHq s Hs ω θ
            (fst (rfJ (suc (suc q)) Hq ε (d , l)))
            (snd (rfJ (suc (suc q)) Hq ε (d , l)))))

-}
