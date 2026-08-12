------------------------------------------------------------------------
-- Bonak.νGpd — V1 direct mirror of Rocq theories/νSet/νGpd.v.
--
-- The groupoid storey of the tower: HSet→HGpd, and the 2-dimensional
-- frame coherences (proved by UIP in νSet) become STORED data
-- (mkCoh2FrameType / Coh2FrameTypeBlock / DepsCohs3), with GUIP
-- (isGroupoid) discharging only the top (coh3Frame is free).
-- Same conventions as Bonak.νSet (see PORTING-NOTES.md): Π-layers,
-- irrelevant Set-valued ≤, interleaved mutual blocks, η-records.
------------------------------------------------------------------------

module Bonak.νGpdBase (arity : Set) where

open import Bonak.Prelude
open import Bonak.LeProp
open import Bonak.RewLemmas

HGpd₀ : Set₁
HGpd₀ = HGpd lzero

-- The type of lists {frame(n,0);...;frame(n,p-1)} for arbitrary k := n-p
mkFrameTypes : ℕ → ℕ → Set₁
mkFrameTypes zero    k = Unit*
mkFrameTypes (suc p) k = Σ[ frames ∈ mkFrameTypes p (suc k) ] HGpd₀

-- The type of lists {painting(n,0);...;painting(n,p-1)} for n := k+p
mkPaintingTypes : (p k : ℕ) → mkFrameTypes p k → Set₁
mkPaintingTypes zero    k _      = Unit*
mkPaintingTypes (suc p) k frames =
  Σ[ paintings ∈ mkPaintingTypes p (suc k) (fst frames) ]
    (GDom (snd frames) → HGpd₀)

-- Mutually: the types of restrFrames and the body of frames
-- (Rocq's RestrFrameTypeBlock, as a plain mutual definition).
-- mkLayer takes the two components of the restrFrames Σ separately so
-- its signature never has to reduce mkRestrFrameTypes.

interleaved mutual

  mkRestrFrameTypes : (p k : ℕ) (frames : mkFrameTypes p k)
                      (paintings : mkPaintingTypes p k frames) → Set
  mkFrames : (p k : ℕ) (frames : mkFrameTypes p k)
             (paintings : mkPaintingTypes p k frames)
             (R : mkRestrFrameTypes p k frames paintings)
             → mkFrameTypes (suc p) k

  mkRestrFrameTypes zero    k frames paintings = ⊤
  mkRestrFrameTypes (suc p) k frames paintings =
    Σ[ R ∈ mkRestrFrameTypes p (suc k) (fst frames) (fst paintings) ]
      ((q : ℕ) .(Hq : q ≤ k) (ε : arity)
       → GDom (snd (mkFrames p (suc k) (fst frames) (fst paintings) R))
       → GDom (snd frames))

  mkLayer : (p k : ℕ) (frames : mkFrameTypes (suc p) k)
            (paintings : mkPaintingTypes (suc p) k frames)
            (R₁ : mkRestrFrameTypes p (suc k) (fst frames) (fst paintings))
            (r : (q : ℕ) .(Hq : q ≤ k) (ε : arity)
                 → GDom (snd (mkFrames p (suc k) (fst frames)
                               (fst paintings) R₁))
                 → GDom (snd frames))
            (d : GDom (snd (mkFrames p (suc k) (fst frames)
                             (fst paintings) R₁)))
            → HGpd₀

  mkLayer p k frames paintings R₁ r d =
    gΠ arity (λ ε → snd paintings (r 0 tt ε d))

  mkFrames zero    k frames paintings R = tt* , gunit
  mkFrames (suc p) k frames paintings R =
    mkFrames p (suc k) (fst frames) (fst paintings) (fst R) ,
    gΣ (snd (mkFrames p (suc k) (fst frames) (fst paintings) (fst R)))
       (λ d → mkLayer p k frames paintings (fst R) (snd R) d)

-- The Deps classes ---------------------------------------------------------

record DepsRestr (p k : ℕ) : Set₁ where
  no-eta-equality; pattern
  constructor depsRestr
  field
    dFrames : mkFrameTypes p k
    dPaintings : mkPaintingTypes p k dFrames
    dRestrFrames : mkRestrFrameTypes p k dFrames dPaintings
open DepsRestr public

toDepsRestr : {p k : ℕ} {frames : mkFrameTypes p k}
              {paintings : mkPaintingTypes p k frames}
              (R : mkRestrFrameTypes p k frames paintings) → DepsRestr p k
toDepsRestr {p} {k} {frames} {paintings} R =
  depsRestr frames paintings R

π₁D : {p k : ℕ} → DepsRestr (suc p) k → DepsRestr p (suc k)
π₁D deps = depsRestr (fst (dFrames deps)) (fst (dPaintings deps))
                     (fst (dRestrFrames deps))

mkFramesD : {p k : ℕ} (deps : DepsRestr p k) → mkFrameTypes (suc p) k
mkFramesD deps = mkFrames _ _ (dFrames deps) (dPaintings deps)
                          (dRestrFrames deps)

mkFrame : {p k : ℕ} (deps : DepsRestr p k) → HGpd₀
mkFrame deps = snd (mkFramesD deps)

data DepsRestrExtension : (p k : ℕ) → DepsRestr p k → Set₁ where
  TopRestrDep : {p : ℕ} {deps : DepsRestr p 0}
                (E : GDom (mkFrame deps) → HGpd₀)
                → DepsRestrExtension p 0 deps
  AddRestrDep : {p k : ℕ} (deps : DepsRestr (suc p) k)
                → DepsRestrExtension (suc p) k deps
                → DepsRestrExtension p (suc k) (π₁D deps)

-- Paintings over the extension ------------------------------------------------

mkPainting : {p k : ℕ} {deps : DepsRestr p k}
             (extraDeps : DepsRestrExtension p k deps)
             → GDom (mkFrame deps) → HGpd₀
mkPainting (TopRestrDep E) d = E d
mkPainting (AddRestrDep deps extraDeps) d =
  gΣ (mkLayer _ _ (dFrames deps) (dPaintings deps)
        (fst (dRestrFrames deps)) (snd (dRestrFrames deps)) d)
     (λ l → mkPainting extraDeps (d , l))

mkPaintingsPrefix : {p k : ℕ} {deps : DepsRestr p k}
                    (extraDeps : DepsRestrExtension p k deps)
                    → mkPaintingTypes p (suc k) (fst (mkFramesD deps))
mkPaintingsPrefix {zero} _ = tt*
mkPaintingsPrefix {suc p} {k} {deps} extraDeps =
  mkPaintingsPrefix (AddRestrDep deps extraDeps) ,
  mkPainting (AddRestrDep deps extraDeps)

mkPaintings : {p k : ℕ} {deps : DepsRestr p k}
              (extraDeps : DepsRestrExtension p k deps)
              → mkPaintingTypes (suc p) k (mkFramesD deps)
mkPaintings extraDeps = mkPaintingsPrefix extraDeps , mkPainting extraDeps

-- restrPainting types ----------------------------------------------------------

mkRestrPaintingType : {p k : ℕ} {deps : DepsRestr (suc p) k}
                      (extraDeps : DepsRestrExtension (suc p) k deps) → Set
mkRestrPaintingType {p} {k} {deps} extraDeps =
  (q : ℕ) .(Hq : q ≤ k) (ε : arity) (d : GDom (mkFrame (π₁D deps)))
  → GDom (mkPainting (AddRestrDep deps extraDeps) d)
  → GDom (snd (dPaintings deps) (snd (dRestrFrames deps) q Hq ε d))

mkRestrPaintingTypes : {p k : ℕ} {deps : DepsRestr p k}
                       (extraDeps : DepsRestrExtension p k deps) → Set
mkRestrPaintingTypes {zero} _ = ⊤
mkRestrPaintingTypes {suc p} {k} {deps} extraDeps =
  Σ[ _ ∈ mkRestrPaintingTypes (AddRestrDep deps extraDeps) ]
    mkRestrPaintingType extraDeps

-- The commuting-square type of a cohFrame over given previous-level
-- restrFrames (νGpd.v factors this out as a named definition).

mkCohFrameType : {p k : ℕ} {deps : DepsRestr (suc p) k}
  (extraDeps : DepsRestrExtension (suc p) k deps)
  (prevRF : mkRestrFrameTypes (suc p) (suc k) (fst (mkFramesD deps))
              (mkPaintings (AddRestrDep deps extraDeps)))
  → Set
mkCohFrameType {p} {k} {deps} extraDeps prevRF =
  (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
  (d : GDom (snd (mkFrames p (suc (suc k))
         (fst (fst (mkFramesD deps)))
         (fst (mkPaintings (AddRestrDep deps extraDeps)))
         (fst prevRF))))
  → snd (dRestrFrames deps) q Hq ε
      (snd prevRF r (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
    ≡ snd (dRestrFrames deps) r (le-trans r q k Hr Hq) ω
      (snd prevRF (suc q) Hq ε d)

-- The restriction of a layer along the new restrFrames, given the
-- previous-level restrFrames and the r = 0 coherences relating them
-- (Rocq's mkRestrLayer; prevRF/coh abstracted like Rocq's prev block,
-- which also keeps this definition out of the mutual clique below).

mkRestrLayer :
  {p k : ℕ} (deps : DepsRestr (suc p) k)
  (extraDeps : DepsRestrExtension (suc p) k deps)
  (rPtop : mkRestrPaintingType extraDeps)
  (prevRF : mkRestrFrameTypes (suc p) (suc k) (fst (mkFramesD deps))
              (mkPaintings (AddRestrDep deps extraDeps)))
  (cohFrame : mkCohFrameType extraDeps prevRF)
  (q : ℕ) .(Hq : q ≤ k) (ε : arity)
  (d : GDom (snd (mkFrames p (suc (suc k))
         (fst (fst (mkFramesD deps)))
         (fst (mkPaintings (AddRestrDep deps extraDeps)))
         (fst prevRF))))
  (l : GDom (mkLayer p (suc k) (fst (mkFramesD deps))
              (mkPaintings (AddRestrDep deps extraDeps))
              (fst prevRF) (snd prevRF) d))
  → GDom (mkLayer p k (dFrames deps) (dPaintings deps)
           (fst (dRestrFrames deps)) (snd (dRestrFrames deps))
           (snd prevRF (suc q) Hq ε d))
mkRestrLayer deps extraDeps rPtop prevRF cohFrame q Hq ε d l ω =
  subst (λ x → GDom (snd (dPaintings deps) x)) (cohFrame q Hq 0 tt ε ω d)
        (rPtop q Hq ε (snd prevRF 0 tt ω d) (l ω))

-- Mutually: the types of cohFrames and the body of restrFrames
-- (Rocq's CohFrameTypeBlock, as a plain mutual definition).

interleaved mutual

  mkCohFrameTypes : {p k : ℕ} {deps : DepsRestr p k}
                    (extraDeps : DepsRestrExtension p k deps)
                    (restrPaintings : mkRestrPaintingTypes extraDeps) → Set
  mkRestrFrames : {p k : ℕ} {deps : DepsRestr p k}
                  (extraDeps : DepsRestrExtension p k deps)
                  (restrPaintings : mkRestrPaintingTypes extraDeps)
                  (Q : mkCohFrameTypes extraDeps restrPaintings)
                  → mkRestrFrameTypes (suc p) k (mkFramesD deps)
                      (mkPaintings extraDeps)

  mkCohFrameTypes {zero} _ _ = ⊤
  mkCohFrameTypes {suc p} {k} {deps} extraDeps restrPaintings =
    Σ[ Q ∈ mkCohFrameTypes (AddRestrDep deps extraDeps)
             (fst restrPaintings) ]
      mkCohFrameType extraDeps
        (mkRestrFrames (AddRestrDep deps extraDeps)
          (fst restrPaintings) Q)

  mkRestrFrames {zero} _ _ _ = tt , λ q Hq ε d → tt
  mkRestrFrames {suc p} {k} {deps} extraDeps restrPaintings Q =
    mkRestrFrames (AddRestrDep deps extraDeps) (fst restrPaintings)
      (fst Q) ,
    λ q Hq ε d →
      snd (mkRestrFrames (AddRestrDep deps extraDeps)
            (fst restrPaintings) (fst Q)) (suc q) Hq ε (fst d) ,
      mkRestrLayer deps extraDeps (snd restrPaintings)
        (mkRestrFrames (AddRestrDep deps extraDeps)
          (fst restrPaintings) (fst Q))
        (snd Q)
        q Hq ε (fst d) (snd d)

-- The DepsCohs class ---------------------------------------------------------

record DepsCohs (p k : ℕ) : Set₁ where
  no-eta-equality; pattern
  constructor depsCohs
  field
    cDeps : DepsRestr p k
    cExtraDeps : DepsRestrExtension p k cDeps
    cRestrPaintings : mkRestrPaintingTypes cExtraDeps
    cCohs : mkCohFrameTypes cExtraDeps cRestrPaintings
open DepsCohs public

toDepsCohs : {p k : ℕ} {deps : DepsRestr p k}
             {extraDeps : DepsRestrExtension p k deps}
             {restrPaintings : mkRestrPaintingTypes extraDeps}
             (cohs : mkCohFrameTypes extraDeps restrPaintings)
             → DepsCohs p k
toDepsCohs {p} {k} {deps} {extraDeps} {restrPaintings} cohs =
  depsCohs deps extraDeps restrPaintings cohs

π₁C : {p k : ℕ} → DepsCohs (suc p) k → DepsCohs p (suc k)
π₁C dc = depsCohs (π₁D (cDeps dc))
                  (AddRestrDep (cDeps dc) (cExtraDeps dc))
                  (fst (cRestrPaintings dc))
                  (fst (cCohs dc))

mkRestrFramesC : {p k : ℕ} (dc : DepsCohs p k)
                 → mkRestrFrameTypes (suc p) k (mkFramesD (cDeps dc))
                     (mkPaintings (cExtraDeps dc))
mkRestrFramesC dc = mkRestrFrames (cExtraDeps dc) (cRestrPaintings dc)
                                  (cCohs dc)

mkDepsRestr : {p k : ℕ} (dc : DepsCohs p k) → DepsRestr (suc p) k
mkDepsRestr dc = depsRestr (mkFramesD (cDeps dc))
                           (mkPaintings (cExtraDeps dc))
                           (mkRestrFramesC dc)

data DepsCohsExtension : (p k : ℕ) → DepsCohs p k → Set₁ where
  TopCohDep : {p : ℕ} {dc : DepsCohs p 0}
              (E : GDom (mkFrame (mkDepsRestr dc)) → HGpd₀)
              → DepsCohsExtension p 0 dc
  AddCohDep : {p k : ℕ} (dc : DepsCohs (suc p) k)
              → DepsCohsExtension (suc p) k dc
              → DepsCohsExtension p (suc k) (π₁C dc)

mkExtraDeps : {p k : ℕ} {dc : DepsCohs p k}
              (eDC : DepsCohsExtension p k dc)
              → DepsRestrExtension (suc p) k (mkDepsRestr dc)
mkExtraDeps (TopCohDep E) = TopRestrDep E
mkExtraDeps (AddCohDep dc eDC) =
  AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC)

-- restrPaintings over the extension --------------------------------------------

mkRestrPainting : {p k : ℕ} {dc : DepsCohs p k}
  (eDC : DepsCohsExtension p k dc)
  (q : ℕ) .(Hq : q ≤ k) (ε : arity)
  (d : GDom (mkFrame (π₁D (mkDepsRestr dc))))
  → GDom (mkPainting (AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC)) d)
  → GDom (mkPainting (cExtraDeps dc) (snd (mkRestrFramesC dc) q Hq ε d))
mkRestrPainting eDC zero Hq ε d (l , c) = l ε
mkRestrPainting (TopCohDep E) (suc q) ()
mkRestrPainting (AddCohDep dc eDC) (suc q) Hq ε d (l , c) =
  mkRestrLayer (cDeps dc) (cExtraDeps dc) (snd (cRestrPaintings dc))
    (mkRestrFramesC (π₁C dc))
    (snd (cCohs dc))
    q Hq ε d l ,
  mkRestrPainting eDC q Hq ε (d , l) c

mkRestrPaintingsPrefix : {p k : ℕ} {dc : DepsCohs p k}
  (eDC : DepsCohsExtension p k dc)
  → mkRestrPaintingTypes
      (AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC))
mkRestrPaintingsPrefix {zero} _ = tt
mkRestrPaintingsPrefix {suc p} {k} {dc} eDC =
  mkRestrPaintingsPrefix (AddCohDep dc eDC) ,
  mkRestrPainting (AddCohDep dc eDC)

mkRestrPaintings : {p k : ℕ} {dc : DepsCohs p k}
  (eDC : DepsCohsExtension p k dc)
  → mkRestrPaintingTypes (mkExtraDeps eDC)
mkRestrPaintings eDC = mkRestrPaintingsPrefix eDC , mkRestrPainting eDC

-- cohPainting types --------------------------------------------------------------

mkCohPaintingType : {p k : ℕ} {dc : DepsCohs (suc p) k}
                    (eDC : DepsCohsExtension (suc p) k dc) → Set
mkCohPaintingType {p} {k} {dc} eDC =
  (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
  (d : GDom (mkFrame (π₁D (mkDepsRestr (π₁C dc)))))
  (c : GDom (mkPainting
         (AddRestrDep (mkDepsRestr (π₁C dc))
           (mkExtraDeps (AddCohDep dc eDC))) d))
  → subst (λ x → GDom (snd (dPaintings (cDeps dc)) x))
      (snd (cCohs dc) q Hq r Hr ε ω d)
      (snd (cRestrPaintings dc) q Hq ε
        (snd (mkRestrFramesC (π₁C dc)) r (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
        (mkRestrPainting (AddCohDep dc eDC) r (le-trans r q (suc k) Hr (le-up q k Hq)) ω d c))
    ≡ snd (cRestrPaintings dc) r (le-trans r q k Hr Hq) ω
        (snd (mkRestrFramesC (π₁C dc)) (suc q) Hq ε d)
        (mkRestrPainting (AddCohDep dc eDC) (suc q) Hq ε d c)

mkCohPaintingTypes : {p k : ℕ} {dc : DepsCohs p k}
                     (eDC : DepsCohsExtension p k dc) → Set
mkCohPaintingTypes {zero} _ = ⊤
mkCohPaintingTypes {suc p} {k} {dc} eDC =
  Σ[ _ ∈ mkCohPaintingTypes (AddCohDep dc eDC) ] mkCohPaintingType eDC


-- The 2-dimensional frame coherence TYPE: stored data in νGpd (in νSet
-- this was proved by isSet) — an s-indexed family of hexagons.
-- Opaque (νGpd.v:692's goal folding, Agda-style): conversion compares
-- mkCoh2FrameType-applications argument-wise instead of unfolding two
-- giant hexagon types; only the definitions that apply an inhabitant
-- (mkCohLayer here, mkCoh2PaintingInstanceType and the mkCoh2Layer*
-- family in νGpd.agda) unfold it.

opaque
  mkCoh2FrameType : {p k : ℕ} {dc : DepsCohs (suc p) k}
    (eDC : DepsCohsExtension (suc p) k dc)
    (prevCohFrames : mkCohFrameTypes
       (AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC))
       (mkRestrPaintingsPrefix eDC))
    → Set
  mkCoh2FrameType {p} {k} {dc} eDC prevCohFrames =
    (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (s : ℕ) .(Hs : s ≤ r)
    (ε ω θ : arity)
    (d : GDom (mkFrame (π₁D (mkDepsRestr (toDepsCohs (fst prevCohFrames))))))
    → cong (λ x → snd (dRestrFrames (cDeps dc)) q Hq ε x)
        (snd prevCohFrames r (le-trans r q (suc k) Hr (le-up q k Hq)) s Hs
          ω θ d)
      ∙ (snd (cCohs dc) q Hq s (le-trans s r q Hs Hr) ε θ
           (snd (mkRestrFramesC (toDepsCohs (fst prevCohFrames))) (suc r)
             (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
      ∙ cong (λ x → snd (dRestrFrames (cDeps dc)) s
                (le-trans s r k Hs (le-trans r q k Hr Hq)) θ x)
          (snd prevCohFrames (suc q) Hq (suc r) Hr ε ω d))
    ≡ snd (cCohs dc) q Hq r Hr ε ω
        (snd (mkRestrFramesC (toDepsCohs (fst prevCohFrames))) s
          (le-up s (suc k) (le-up s k
            (le-trans s r k Hs (le-trans r q k Hr Hq)))) θ d)
      ∙ (cong (λ x → snd (dRestrFrames (cDeps dc)) r (le-trans r q k Hr Hq)
                ω x)
          (snd prevCohFrames (suc q) Hq s
            (le-up s q (le-trans s r q Hs Hr)) ε θ d)
      ∙ snd (cCohs dc) r (le-trans r q k Hr Hq) s Hs ω θ
          (snd (mkRestrFramesC (toDepsCohs (fst prevCohFrames)))
            (suc (suc q)) Hq ε d))

-- The layer coherence (νGpd's mkCohLayer): as in νSet, but the
-- 2-dimensional frame coherence premise is the STORED coh2Frame data.

module _ {p k : ℕ} {dc : DepsCohs (suc p) k}
  (eDC : DepsCohsExtension (suc p) k dc)
  (cohPainting : mkCohPaintingType eDC)
  (prevCohFrames : mkCohFrameTypes
     (AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC))
     (mkRestrPaintingsPrefix eDC))
  (coh2Frame : mkCoh2FrameType eDC prevCohFrames)
  where

  private
    dcI : DepsCohs p (suc (suc k))
    dcI = toDepsCohs (fst prevCohFrames)

    prevRF = mkRestrFramesC dcI

    innerRL = mkRestrLayer (π₁D (mkDepsRestr dc))
                (AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC))
                (snd (mkRestrPaintingsPrefix eDC)) prevRF
                (snd prevCohFrames)
    outerRL = mkRestrLayer (cDeps dc) (cExtraDeps dc)
                (snd (cRestrPaintings dc)) (mkRestrFramesC (π₁C dc))
                (snd (cCohs dc))

  opaque
    unfolding mkCoh2FrameType

    mkCohLayer :
      (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
      (d : GDom (mkFrame (π₁D (mkDepsRestr dcI))))
      (l : GDom (mkLayer p (suc (suc k)) (mkFramesD (cDeps dcI))
                  (mkPaintings (cExtraDeps dcI))
                  (fst prevRF) (snd prevRF) d))
      → subst (λ x → GDom (mkLayer p k (dFrames (cDeps dc))
                            (dPaintings (cDeps dc))
                            (fst (dRestrFrames (cDeps dc)))
                            (snd (dRestrFrames (cDeps dc))) x))
          (snd prevCohFrames (suc q) Hq (suc r) Hr ε ω d)
          (outerRL q Hq ε
            (snd prevRF (suc r) (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
            (innerRL r (le-trans r q (suc k) Hr (le-up q k Hq)) ω d l))
        ≡ outerRL r (le-trans r q k Hr Hq) ω
            (snd prevRF (suc (suc q)) Hq ε d)
            (innerRL (suc q) Hq ε d l)
    mkCohLayer q Hq r Hr ε ω d l =
      Π-subst-ext
        {B = λ ω' x → GDom (snd (dPaintings (cDeps dc))
                        (snd (dRestrFrames (cDeps dc)) 0 tt ω' x))}
        (snd prevCohFrames (suc q) Hq (suc r) Hr ε ω d)
        (λ θ → rew-cohLayer33
          {P = λ x → GDom (snd (dPaintings (cDeps dc)) x)}
          {S2 = λ m → GDom (mkPainting
                  (AddRestrDep (cDeps dc) (cExtraDeps dc)) m)}
          {S3 = λ m → GDom (mkPainting
                  (AddRestrDep (cDeps dc) (cExtraDeps dc)) m)}
          {rf0 = λ x → snd (dRestrFrames (cDeps dc)) 0 tt θ x}
          {rfF = λ m → snd (dRestrFrames (cDeps dc)) q Hq ε m}
          {rfG = λ m → snd (dRestrFrames (cDeps dc)) r
                         (le-trans r q k Hr Hq) ω m}
          {F = λ m c → snd (cRestrPaintings dc) q Hq ε m c}
          {G = λ m c → snd (cRestrPaintings dc) r
                         (le-trans r q k Hr Hq) ω m c}
          (cohPainting q Hq r Hr ε ω (snd prevRF 0 tt θ d) (l θ))
          (coh2Frame q Hq r Hr 0 tt ε ω θ d))

-- Mutually: the types of coh2Frames and the body of cohFrames
-- (Rocq's Coh2FrameTypeBlock, as a plain mutual definition).

interleaved mutual

  mkCoh2FrameTypes : {p k : ℕ} {dc : DepsCohs p k}
                     (eDC : DepsCohsExtension p k dc)
                     (cohPaintings : mkCohPaintingTypes eDC) → Set
  mkCohFrames : {p k : ℕ} {dc : DepsCohs p k}
                (eDC : DepsCohsExtension p k dc)
                (cohPaintings : mkCohPaintingTypes eDC)
                (Q2 : mkCoh2FrameTypes eDC cohPaintings)
                → mkCohFrameTypes (mkExtraDeps eDC) (mkRestrPaintings eDC)

  mkCoh2FrameTypes {zero} _ _ = ⊤
  mkCoh2FrameTypes {suc p} {k} {dc} eDC cohPaintings =
    Σ[ Q2 ∈ mkCoh2FrameTypes (AddCohDep dc eDC) (fst cohPaintings) ]
      mkCoh2FrameType eDC
        (mkCohFrames (AddCohDep dc eDC) (fst cohPaintings) Q2)

  mkCohFrames {zero} eDC cohPaintings _ =
    tt , λ q Hq r Hr ε ω d → refl
  mkCohFrames {suc p} {k} {dc} eDC cohPaintings Q2 =
    mkCohFrames (AddCohDep dc eDC) (fst cohPaintings) (fst Q2) ,
    λ q Hq r Hr ε ω d →
      Σ≡ (snd (mkCohFrames (AddCohDep dc eDC) (fst cohPaintings)
                (fst Q2)) (suc q) Hq (suc r) Hr ε ω (fst d))
         (mkCohLayer eDC (snd cohPaintings)
           (mkCohFrames (AddCohDep dc eDC) (fst cohPaintings) (fst Q2))
           (snd Q2) q Hq r Hr ε ω (fst d) (snd d))

