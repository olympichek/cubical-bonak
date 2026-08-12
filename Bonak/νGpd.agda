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

module Bonak.νGpd (arity : Set) where

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
  → PathP (λ i → GDom (snd (dPaintings (cDeps dc))
                        (snd (cCohs dc) q Hq r Hr ε ω d i)))
      (snd (cRestrPaintings dc) q Hq ε
        (snd (mkRestrFramesC (π₁C dc)) r (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
        (mkRestrPainting (AddCohDep dc eDC) r (le-trans r q (suc k) Hr (le-up q k Hq)) ω d c))
      (snd (cRestrPaintings dc) r (le-trans r q k Hr Hq) ω
        (snd (mkRestrFramesC (π₁C dc)) (suc q) Hq ε d)
        (mkRestrPainting (AddCohDep dc eDC) (suc q) Hq ε d c))

mkCohPaintingTypes : {p k : ℕ} {dc : DepsCohs p k}
                     (eDC : DepsCohsExtension p k dc) → Set
mkCohPaintingTypes {zero} _ = ⊤
mkCohPaintingTypes {suc p} {k} {dc} eDC =
  Σ[ _ ∈ mkCohPaintingTypes (AddCohDep dc eDC) ] mkCohPaintingType eDC


-- The 2-dimensional frame coherence TYPE: stored data in νGpd (in νSet
-- this was proved by isSet) — an s-indexed family of hexagons.

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
   → Square
       (snd (cCohs dc) q Hq r Hr ε ω
         (snd (mkRestrFramesC (toDepsCohs (fst prevCohFrames))) s
           (le-up s (suc k) (le-up s k
             (le-trans s r k Hs (le-trans r q k Hr Hq)))) θ d))
       (cong (λ x → snd (dRestrFrames (cDeps dc)) s
                (le-trans s r k Hs (le-trans r q k Hr Hq)) θ x)
          (snd prevCohFrames (suc q) Hq (suc r) Hr ε ω d))
       (cong (λ x → snd (dRestrFrames (cDeps dc)) q Hq ε x)
          (snd prevCohFrames r (le-trans r q (suc k) Hr (le-up q k Hq))
            s Hs ω θ d)
        ∙ snd (cCohs dc) q Hq s (le-trans s r q Hs Hr) ε θ
            (snd (mkRestrFramesC (toDepsCohs (fst prevCohFrames))) (suc r)
              (le-trans r q (suc k) Hr (le-up q k Hq)) ω d))
       (cong (λ x → snd (dRestrFrames (cDeps dc)) r (le-trans r q k Hr Hq)
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
      → PathP (λ i → GDom (mkLayer p k (dFrames (cDeps dc))
                            (dPaintings (cDeps dc))
                            (fst (dRestrFrames (cDeps dc)))
                            (snd (dRestrFrames (cDeps dc)))
                            (snd prevCohFrames (suc q) Hq (suc r) Hr ε ω d i)))
          (outerRL q Hq ε
            (snd prevRF (suc r) (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
            (innerRL r (le-trans r q (suc k) Hr (le-up q k Hq)) ω d l))
          (outerRL r (le-trans r q k Hr Hq) ω
            (snd prevRF (suc (suc q)) Hq ε d)
            (innerRL (suc q) Hq ε d l))
    mkCohLayer q Hq r Hr ε ω d l i θ =
      cohLayer-squareP
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
        {E1 = snd prevCohFrames (suc q) Hq (suc r) Hr ε ω d}
        {C2 = snd prevCohFrames r
                (le-trans r q (suc k) Hr (le-up q k Hq)) 0 tt ω θ d}
        {D2 = snd prevCohFrames (suc q) Hq 0 tt ε θ d}
        {C1 = snd (cCohs dc) q Hq 0 tt ε θ
                (snd prevRF (suc r)
                  (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)}
        {D1 = snd (cCohs dc) r (le-trans r q k Hr Hq) 0 tt ω θ
                (snd prevRF (suc (suc q)) Hq ε d)}
        {K = snd (cCohs dc) q Hq r Hr ε ω (snd prevRF 0 tt θ d)}
        (cohPainting q Hq r Hr ε ω (snd prevRF 0 tt θ d) (l θ))
        (coh2Frame q Hq r Hr 0 tt ε ω θ d)
        i

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
    λ q Hq r Hr ε ω d i →
      snd (mkCohFrames (AddCohDep dc eDC) (fst cohPaintings)
            (fst Q2)) (suc q) Hq (suc r) Hr ε ω (fst d) i ,
      mkCohLayer eDC (snd cohPaintings)
        (mkCohFrames (AddCohDep dc eDC) (fst cohPaintings) (fst Q2))
        (snd Q2) q Hq r Hr ε ω (fst d) (snd d) i

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

-- The painting coherence (νGpd's mkCohPainting), PathP-native: the
-- r = 0 case is the subst-filler of mkRestrLayer's transport, and the
-- r,q ≥ 1 case pairs the stored mkCohLayer with the recursive call
-- definitionally (V1 needed Σ≡dep).

mkCohPainting : {p k : ℕ} {dc2 : DepsCohs2 p k}
                (eDC2 : DepsCohs2Extension p k dc2)
                → mkCohPaintingType (mkExtraCohs eDC2)
mkCohPainting {dc2 = dc2} eDC2 q Hq zero Hr ε ω d (l , c) =
  subst-filler
    (λ x → GDom (snd (dPaintings (cDeps (mkDepsCohs dc2))) x))
    (snd (cCohs (mkDepsCohs dc2)) q Hq 0 Hr ε ω d)
    (snd (cRestrPaintings (mkDepsCohs dc2)) q Hq ε
      (snd (mkRestrFramesC (π₁C (mkDepsCohs dc2))) 0
        (le-trans 0 q (suc _) Hr (le-up q _ Hq)) ω d)
      (l ω))
mkCohPainting eDC2 zero Hq (suc r) () ε ω d c
mkCohPainting (TopCoh2Dep E) (suc q) () (suc r) Hr ε ω d c
mkCohPainting (AddCoh2Dep dc2 eDC2) (suc q) Hq (suc r) Hr ε ω d (l , c) i =
  mkCohLayer (c2ExtraDepsCohs dc2) (snd (c2CohPaintings dc2)) prev
    (snd (c2Coh2Frames dc2)) q Hq r Hr ε ω d l i ,
  mkCohPainting eDC2 q Hq r Hr ε ω (d , l) c i
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
-- V2: the coh2Painting statement is a SquareP over the STORED
-- coh2Frame square — no Source/FrameEndpoint/Endpoint/Instance
-- subst-ladder (V1's νGpd.agda:118-262): a PathP family names its own
-- endpoints, so there is nothing left to name.  Composite sides use
-- compPathP, `sigT-map-eq f p` becomes the dependent cong
-- `λ i → f (base i) (p i)`.
------------------------------------------------------------------------

opaque
  unfolding mkCoh2FrameType

  mkCoh2PaintingType : {p k : ℕ}
    (dc2 : DepsCohs2 (suc p) k)
    (eDC2 : DepsCohs2Extension (suc p) k dc2) → Set
  mkCoh2PaintingType {p} {k} dc2 eDC2 =
    (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (s : ℕ) .(Hs : s ≤ r)
    (ε ω θ : arity)
    (d : GDom (mkFrame (π₁D (mkDepsRestr (π₁C (π₁C (mkDepsCohs dc2)))))))
    (c : GDom (mkPainting
           (AddRestrDep (mkDepsRestr (π₁C (π₁C (mkDepsCohs dc2))))
             (mkExtraDeps (AddCohDep (π₁C (mkDepsCohs dc2))
               (AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2))))) d)) →
    let dc = c2DepsCohs dc2
        prev = mkCohFrames (AddCohDep dc (c2ExtraDepsCohs dc2))
                 (fst (c2CohPaintings dc2)) (fst (c2Coh2Frames dc2))
        rP = snd (cRestrPaintings dc)
        cP = snd (c2CohPaintings dc2)
        cP2 = mkCohPainting (AddCoh2Dep dc2 eDC2)
        rF2 = snd (mkRestrFramesC (π₁C (π₁C (mkDepsCohs dc2))))
        rP2 = mkRestrPainting (AddCohDep (π₁C (mkDepsCohs dc2))
                (AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2)))
        P₀ = λ x → GDom (snd (dPaintings (cDeps dc)) x)
        HrHq↑ = le-trans r q (suc k) Hr (le-up q k Hq)
        HrHq = le-trans r q k Hr Hq
        HsHrHq = le-trans s r k Hs HrHq
        HsHr = le-trans s r q Hs Hr
        HsHrHq↑↑ = le-up s (suc k) (le-up s k HsHrHq)
    in SquareP
         (λ m i → P₀ (snd (c2Coh2Frames dc2) q Hq r Hr s Hs ε ω θ d m i))
         (cP q Hq r Hr ε ω (rF2 s HsHrHq↑↑ θ d) (rP2 s HsHrHq↑↑ θ d c))
         (λ i → rP s HsHrHq θ (snd prev (suc q) Hq (suc r) Hr ε ω d i)
                  (cP2 (suc q) Hq (suc r) Hr ε ω d c i))
         (compPathP {P = P₀}
            (λ i → rP q Hq ε (snd prev r HrHq↑ s Hs ω θ d i)
                     (cP2 r HrHq↑ s Hs ω θ d c i))
            (cP q Hq s HsHr ε θ
               (rF2 (suc r) HrHq↑ ω d) (rP2 (suc r) HrHq↑ ω d c)))
         (compPathP {P = P₀}
            (λ i → rP r HrHq ω
                     (snd prev (suc q) Hq s (le-up s q HsHr) ε θ d i)
                     (cP2 (suc q) Hq s (le-up s q HsHr) ε θ d c i))
            (cP r HrHq s Hs ω θ
               (rF2 (suc (suc q)) Hq ε d) (rP2 (suc (suc q)) Hq ε d c)))

mkCoh2PaintingTypes : {p k : ℕ} {dc2 : DepsCohs2 p k}
  (eDC2 : DepsCohs2Extension p k dc2) → Set
mkCoh2PaintingTypes {zero} _ = ⊤
mkCoh2PaintingTypes {suc p} {k} {dc2} eDC2 =
  Σ[ _ ∈ mkCoh2PaintingTypes (AddCoh2Dep dc2 eDC2) ]
    mkCoh2PaintingType dc2 eDC2

------------------------------------------------------------------------
-- Part 3b (NOT LANDED — see the measurements below): mkCoh2Layer,
-- mkCoh2Frames, DepsCohs3, mkCoh2Painting, νGpdData.
--
-- The V2 design, for the record.  mkCoh2Layer is a SquareP of layers
-- over the previous storey's stored coh2Frame square; layers are Π, so
-- a SquareP of layers is pointwise a function into SquarePs
-- definitionally (V1's lmap2_hex_rew_eq bridge has no counterpart).
-- With the part-3b ladder
--
--   prev1  = mkCohFrames (AddCohDep (c2DepsCohs dc2) (c2ExtraDepsCohs dc2))
--              (fst (c2CohPaintings dc2)) (fst (c2Coh2Frames dc2))
--   prevCF = mkCohFrames (AddCohDep (mkDepsCohs (π₁C2 dc2))
--              (mkExtraCohs (AddCoh2Dep dc2 eDC2)))
--              (fst (mkCohPaintings (AddCoh2Dep dc2 eDC2)))
--              (fst prevCoh2Frames)
--   dcI    = toDepsCohs (fst prevCF)                  -- bound suc³ k
--   dcJ    = depsCohs (mkDepsRestr (toDepsCohs (fst prev1))) …  -- suc² k
--   CL1    = mkCohLayer (c2ExtraDepsCohs dc2) (snd (c2CohPaintings dc2))
--              prev1 (snd (c2Coh2Frames dc2))
--   CL2    = mkCohLayer (mkExtraCohs (AddCoh2Dep dc2 eDC2))
--              (mkCohPainting (AddCoh2Dep dc2 eDC2)) prevCF
--              (snd prevCoh2Frames)
--   RL0    = mkRestrLayer (cDeps (c2DepsCohs dc2)) … (snd (cCohs …))
--   rfJ    = snd (mkRestrFramesC dcJ)
--
-- the statement is (d, l at the dcI storey):
--
--   SquareP (λ m i → QL (snd prevCoh2Frames (suc q) (suc r) (suc s)
--                          ε ω θ d m i))
--     (CL1 q r ε ω (fst (rfJ s θ (d , l))) (snd (rfJ s θ (d , l))))
--     (λ i → RL0 s θ (snd prevCF (suc² q) (suc² r) ε ω d i)
--                    (CL2 (suc q) (suc r) ε ω d l i))
--     (compPathP {P = QL}
--        (λ i → RL0 q ε (snd prevCF (suc r) (suc s) ω θ d i)
--                       (CL2 r s ω θ d l i))
--        (CL1 q s ε θ (fst (rfJ (suc r) ω (d , l)))
--                     (snd (rfJ (suc r) ω (d , l)))))
--     (compPathP {P = QL}
--        (λ i → RL0 r ω (snd prevCF (suc² q) (suc s) ε θ d i)
--                       (CL2 (suc q) s ε θ d l i))
--        (CL1 r s ω θ (fst (rfJ (suc² q) ε (d , l)))
--                     (snd (rfJ (suc² q) ε (d , l)))))
--
-- i.e. exactly the four sides of mkCoh2FrameType, one storey up in the
-- layer fibres: `sigT_map_eq f p` is the dependent cong
-- `λ i → f (base i) (p i)` and `⊙` is compPathP.  The proof is one cube:
-- faces = the stored coh2Painting SquareP (this storey's premise), the
-- stored coh2Frame squares, and the four cohPainting-side fillers,
-- closed by ONE isGroupoid→Cube (RewLemmas) — the cubical form of
-- Rocq's single GUIP at νGpd.v:918.  No rew_coh2Layer, no
-- permutahedral_coherence, no κ-conjugation.
--
-- WHY IT IS NOT LANDED — a conversion wall, not a proof gap.  Measured
-- here (Agda 2.8.0, this machine; everything that IS in this file
-- rechecks in 5 s):
--
--   * Rung 1 (broken, fix applied above).  The recursive-call rung of
--     mkCoh2Frames is the conversion
--       mkCoh2FrameTypes A B ≟ mkCoh2FrameTypes A′ B
--     where A′ is A after ONE delta step (mkExtraCohs (AddCoh2Dep dc2
--     eDC2) versus AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2)).
--     Transparent: > 100 s, no result — Agda has no compare-args
--     shortcut for equal defined heads, so it unfolds mkCoh2FrameType on
--     both sides and compares the two giant Squares.  The same
--     conversion one storey lower (mkCohPaintingTypes) takes 0.8 s.
--     With mkCoh2FrameType `opaque` (Rocq's νGpd.v:692 goal-folding,
--     which exists for exactly this reason) the rung is INSTANT — hence
--     the opaque block above, with `unfolding` only where the type has
--     to expose its Π (mkCohLayer, mkCoh2PaintingType).
--
--   * Rung 2 (open).  Building the top coh2Frame square needs
--     mkCoh2FrameType unfolded, and merely ELABORATING that instance
--     type at the top storey does not finish: > 150 s even with the
--     whole square admitted, and > 3 min with the Prefix/top split
--     (mkCoh2FramesPrefix outside the unfolding block, mkCoh2Frame
--     inside).  This is the cost of the type itself — its sides contain
--     mkRestrFramesC (toDepsCohs (fst (mkCohFrames …))) three storeys
--     deep — not of any proof term.  V1 (main) is stuck at the same
--     place; the ETA FIX bought the storey below, this one needs
--     folding at the mkCohFrames / mkRestrFramesC level too (or the
--     conversion cache).
--
--   * Rung 2, localised (round 2).  It is not the Square types and not
--     any proof term: with mkCoh2FrameType already opaque, elaborating
--     the single application
--       mkCohFrames (AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2)) cps Q2
--     with cps and Q2 ABSTRACT and every spelling syntactically equal to
--     the expected types already does not terminate (> 70 s), while the
--     same telescope without the application takes 0.4 s and the same
--     application with an ABSTRACT extension takes 0.3 s
--     (probes/P05-rung2.agda).  The cost is the type-level unfolding of
--     the tower functions (mkExtraDeps / mkRestrPaintings /
--     mkCohFrameTypes / mkRestrFrames) at a constructor-headed extension
--     one storey up.  It is specific to THAT storey: the same
--     application one storey lower (mkRestrFrames at a concrete
--     extension) takes 0.4 s — probes/P06-lower.agda.
--   * More folding is the right tool but Agda 2.8.0 blocks it:
--     `unfolding` is BODY-ONLY (probes/P04-unfold.agda), and this
--     tower applies coherence data inside type SIGNATURES (mkCohLayer's
--     PathP).  Folding mkCohFrameType therefore requires first turning
--     every such statement into a named definition (mkCohLayerType,
--     mkCoh2LayerType, … — Rocq's νGpd.v:692 trick, which thereby gains
--     a second, Agda-specific justification).  Opacifying the
--     mkCoh2FrameTypes ⋈ mkCohFrames mutual as a whole does NOT work:
--     π₁C2 then cannot project it, and π₁-commutation
--     (mkDepsCohs (π₁C2 dc2) ≡ π₁C (mkDepsCohs dc2)) breaks.
--   * Conversion cache (Agda 2.9.0-dev, ~/agda-dev): the same
--     reproducer does not finish in 15 min either with or without
--     AGDA_CONVERSION_CACHE=1 (5-6 GB RSS and climbing in both), and
--     2.8.0 does not finish it in 25 min either (4.9 GB RSS).  The cache does not turn this
--     rung from unbounded into bounded.
--   * Spelling discipline (measured, useful whatever the fix).  At this
--     storey a term must be spelled EXACTLY as the reduct of the
--     consumer's type spells it: naming a storey (dcT = mkDepsCohs
--     (π₁C2 dc2)) and using the name inside mkCohLayer's arguments turns
--     a 12 s check into minutes; with raw spellings CL1/CL2 applied to
--     (d, l) check in 4-25 s.
------------------------------------------------------------------------
