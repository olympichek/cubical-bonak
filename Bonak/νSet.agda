------------------------------------------------------------------------
-- Bonak.νSet — V1 direct mirror of Rocq theories/νSet/νSet.v.
--
-- Parameterized by the arity alone: with funExt computing in Cubical
-- Agda, the layer former is uniformly `(ε : arity) → B ε` (LayerSig's
-- nth = application, lam = identity, ext = funExt), so simplicial = ⊤,
-- cubical = Bool.
--
-- Rocq's RestrFrameTypeBlock / CohFrameTypeBlock helper classes become
-- plain mutual definitions; the Deps* classes become η-records; the
-- two Extension inductives keep p as an index (it is a non-uniform
-- parameter in Rocq); SProp bounds are Set-valued recursive ≤ with
-- irrelevant proof arguments (Bonak.LeProp, see probes/P01).
------------------------------------------------------------------------

module Bonak.νSet (arity : Set) where

open import Bonak.Prelude
open import Bonak.LeProp
open import Bonak.RewLemmas

HSet₀ : Set₁
HSet₀ = HSet lzero

-- The type of lists {frame(n,0);...;frame(n,p-1)} for arbitrary k := n-p
mkFrameTypes : ℕ → ℕ → Set₁
mkFrameTypes zero    k = Unit*
mkFrameTypes (suc p) k = Σ[ frames ∈ mkFrameTypes p (suc k) ] HSet₀

-- The type of lists {painting(n,0);...;painting(n,p-1)} for n := k+p
mkPaintingTypes : (p k : ℕ) → mkFrameTypes p k → Set₁
mkPaintingTypes zero    k _      = Unit*
mkPaintingTypes (suc p) k frames =
  Σ[ paintings ∈ mkPaintingTypes p (suc k) (fst frames) ]
    (Dom (snd frames) → HSet₀)

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
       → Dom (snd (mkFrames p (suc k) (fst frames) (fst paintings) R))
       → Dom (snd frames))

  mkLayer : (p k : ℕ) (frames : mkFrameTypes (suc p) k)
            (paintings : mkPaintingTypes (suc p) k frames)
            (R₁ : mkRestrFrameTypes p (suc k) (fst frames) (fst paintings))
            (r : (q : ℕ) .(Hq : q ≤ k) (ε : arity)
                 → Dom (snd (mkFrames p (suc k) (fst frames)
                               (fst paintings) R₁))
                 → Dom (snd frames))
            (d : Dom (snd (mkFrames p (suc k) (fst frames)
                             (fst paintings) R₁)))
            → HSet₀

  mkLayer p k frames paintings R₁ r d =
    hΠ arity (λ ε → snd paintings (r 0 tt ε d))

  mkFrames zero    k frames paintings R = tt* , hunit
  mkFrames (suc p) k frames paintings R =
    mkFrames p (suc k) (fst frames) (fst paintings) (fst R) ,
    hΣ (snd (mkFrames p (suc k) (fst frames) (fst paintings) (fst R)))
       (λ d → mkLayer p k frames paintings (fst R) (snd R) d)

-- The Deps classes ---------------------------------------------------------

record DepsRestr (p k : ℕ) : Set₁ where
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

mkFrame : {p k : ℕ} (deps : DepsRestr p k) → HSet₀
mkFrame deps = snd (mkFramesD deps)

data DepsRestrExtension : (p k : ℕ) → DepsRestr p k → Set₁ where
  TopRestrDep : {p : ℕ} {deps : DepsRestr p 0}
                (E : Dom (mkFrame deps) → HSet₀)
                → DepsRestrExtension p 0 deps
  AddRestrDep : {p k : ℕ} (deps : DepsRestr (suc p) k)
                → DepsRestrExtension (suc p) k deps
                → DepsRestrExtension p (suc k) (π₁D deps)

-- Paintings over the extension ------------------------------------------------

mkPainting : {p k : ℕ} {deps : DepsRestr p k}
             (extraDeps : DepsRestrExtension p k deps)
             → Dom (mkFrame deps) → HSet₀
mkPainting (TopRestrDep E) d = E d
mkPainting (AddRestrDep deps extraDeps) d =
  hΣ (mkLayer _ _ (dFrames deps) (dPaintings deps)
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
  (q : ℕ) .(Hq : q ≤ k) (ε : arity) (d : Dom (mkFrame (π₁D deps)))
  → Dom (mkPainting (AddRestrDep deps extraDeps) d)
  → Dom (snd (dPaintings deps) (snd (dRestrFrames deps) q Hq ε d))

mkRestrPaintingTypes : {p k : ℕ} {deps : DepsRestr p k}
                       (extraDeps : DepsRestrExtension p k deps) → Set
mkRestrPaintingTypes {zero} _ = ⊤
mkRestrPaintingTypes {suc p} {k} {deps} extraDeps =
  Σ[ _ ∈ mkRestrPaintingTypes (AddRestrDep deps extraDeps) ]
    mkRestrPaintingType extraDeps

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
  (coh : (q : ℕ) .(Hq : q ≤ k) (ε ω : arity)
         (d : Dom (snd (mkFrames p (suc (suc k))
                (fst (fst (mkFramesD deps)))
                (fst (mkPaintings (AddRestrDep deps extraDeps)))
                (fst prevRF))))
       → snd (dRestrFrames deps) q Hq ε (snd prevRF 0 tt ω d)
         ≡ snd (dRestrFrames deps) 0 tt ω (snd prevRF (suc q) Hq ε d))
  (q : ℕ) .(Hq : q ≤ k) (ε : arity)
  (d : Dom (snd (mkFrames p (suc (suc k))
         (fst (fst (mkFramesD deps)))
         (fst (mkPaintings (AddRestrDep deps extraDeps)))
         (fst prevRF))))
  (l : Dom (mkLayer p (suc k) (fst (mkFramesD deps))
              (mkPaintings (AddRestrDep deps extraDeps))
              (fst prevRF) (snd prevRF) d))
  → Dom (mkLayer p k (dFrames deps) (dPaintings deps)
           (fst (dRestrFrames deps)) (snd (dRestrFrames deps))
           (snd prevRF (suc q) Hq ε d))
mkRestrLayer deps extraDeps rPtop prevRF coh q Hq ε d l ω =
  subst (λ x → Dom (snd (dPaintings deps) x)) (coh q Hq ε ω d)
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
      ((q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
       (d : Dom (snd (mkFrames p (suc (suc k))
              (fst (fst (mkFramesD deps)))
              (fst (mkPaintings (AddRestrDep deps extraDeps)))
              (fst (mkRestrFrames (AddRestrDep deps extraDeps)
                     (fst restrPaintings) Q)))))
       → snd (dRestrFrames deps) q Hq ε
           (snd (mkRestrFrames (AddRestrDep deps extraDeps)
                  (fst restrPaintings) Q) r (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
         ≡ snd (dRestrFrames deps) r (le-trans r q k Hr Hq) ω
           (snd (mkRestrFrames (AddRestrDep deps extraDeps)
                  (fst restrPaintings) Q) (suc q) Hq ε d))

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
        (λ q' Hq' ε' ω' d' → snd Q q' Hq' 0 tt ε' ω' d')
        q Hq ε (fst d) (snd d)

-- The DepsCohs class ---------------------------------------------------------

record DepsCohs (p k : ℕ) : Set₁ where
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
              (E : Dom (mkFrame (mkDepsRestr dc)) → HSet₀)
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
  (d : Dom (mkFrame (π₁D (mkDepsRestr dc))))
  → Dom (mkPainting (AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC)) d)
  → Dom (mkPainting (cExtraDeps dc) (snd (mkRestrFramesC dc) q Hq ε d))
mkRestrPainting eDC zero Hq ε d (l , c) = l ε
mkRestrPainting (TopCohDep E) (suc q) ()
mkRestrPainting (AddCohDep dc eDC) (suc q) Hq ε d (l , c) =
  mkRestrLayer (cDeps dc) (cExtraDeps dc) (snd (cRestrPaintings dc))
    (mkRestrFramesC (π₁C dc))
    (λ q' Hq' ε' ω' d' → snd (cCohs dc) q' Hq' 0 tt ε' ω' d')
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
  (d : Dom (mkFrame (π₁D (mkDepsRestr (π₁C dc)))))
  (c : Dom (mkPainting
         (AddRestrDep (mkDepsRestr (π₁C dc))
           (mkExtraDeps (AddCohDep dc eDC))) d))
  → subst (λ x → Dom (snd (dPaintings (cDeps dc)) x))
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
