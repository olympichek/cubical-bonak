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

-- The 2-dimensional frame coherence, from the frames being HSets
-- (Rocq's mkCoh2Frame, proved by UIP) -----------------------------------------

mkCoh2Frame : {p k : ℕ} {dc : DepsCohs (suc p) k}
  (eDC : DepsCohsExtension (suc p) k dc)
  (prevCohFrames : mkCohFrameTypes
     (AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC))
     (mkRestrPaintingsPrefix eDC))
  (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω θ : arity)
  (d : Dom (mkFrame (π₁D (mkDepsRestr (toDepsCohs (fst prevCohFrames))))))
  → cong (λ x → snd (dRestrFrames (cDeps dc)) q Hq ε x)
      (snd prevCohFrames r (le-trans r q (suc k) Hr (le-up q k Hq)) 0 tt
        ω θ d)
    ∙ᵗ snd (cCohs dc) q Hq 0 tt ε θ
         (snd (mkRestrFramesC (toDepsCohs (fst prevCohFrames))) (suc r)
           (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
    ∙ᵗ cong (λ x → snd (dRestrFrames (cDeps dc)) 0 tt θ x)
        (snd prevCohFrames (suc q) Hq (suc r) Hr ε ω d)
  ≡ snd (cCohs dc) q Hq r Hr ε ω
      (snd (mkRestrFramesC (toDepsCohs (fst prevCohFrames))) 0 tt θ d)
    ∙ᵗ cong (λ x → snd (dRestrFrames (cDeps dc)) r (le-trans r q k Hr Hq)
              ω x)
        (snd prevCohFrames (suc q) Hq 0 tt ε θ d)
    ∙ᵗ snd (cCohs dc) r (le-trans r q k Hr Hq) 0 tt ω θ
        (snd (mkRestrFramesC (toDepsCohs (fst prevCohFrames)))
          (suc (suc q)) Hq ε d)
mkCoh2Frame {dc = dc} eDC prevCohFrames q Hq r Hr ε ω θ d =
  isSetDom (snd (dFrames (cDeps dc))) _ _ _ _

-- The layer coherence (Rocq's mkCohLayer): a Π-layer bridge step, then
-- the fused rew-cohLayer33 with the painting coherence and mkCoh2Frame
-- as premises.

module _ {p k : ℕ} {dc : DepsCohs (suc p) k}
  (eDC : DepsCohsExtension (suc p) k dc)
  (cohPaintings : mkCohPaintingTypes eDC)
  (prevCohFrames : mkCohFrameTypes
     (AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC))
     (mkRestrPaintingsPrefix eDC))
  where

  private
    dcI : DepsCohs p (suc (suc k))
    dcI = toDepsCohs (fst prevCohFrames)

    prevRF = mkRestrFramesC dcI

    -- the two mkRestrLayer instances of the statement
    innerRL = mkRestrLayer (π₁D (mkDepsRestr dc))
                (AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC))
                (snd (mkRestrPaintingsPrefix eDC)) prevRF
                (λ q' Hq' ε' ω' d' →
                   snd prevCohFrames q' Hq' 0 tt ε' ω' d')
    outerRL = mkRestrLayer (cDeps dc) (cExtraDeps dc)
                (snd (cRestrPaintings dc)) (mkRestrFramesC (π₁C dc))
                (λ q' Hq' ε' ω' d' →
                   snd (cCohs dc) q' Hq' 0 tt ε' ω' d')

  mkCohLayer :
    (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
    (d : Dom (mkFrame (π₁D (mkDepsRestr dcI))))
    (l : Dom (mkLayer p (suc (suc k)) (mkFramesD (cDeps dcI))
                (mkPaintings (cExtraDeps dcI))
                (fst prevRF) (snd prevRF) d))
    → subst (λ x → Dom (mkLayer p k (dFrames (cDeps dc))
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
      {B = λ ω' x → Dom (snd (dPaintings (cDeps dc))
                      (snd (dRestrFrames (cDeps dc)) 0 tt ω' x))}
      (snd prevCohFrames (suc q) Hq (suc r) Hr ε ω d)
      (λ θ → rew-cohLayer33ᵗ
        {P = λ x → Dom (snd (dPaintings (cDeps dc)) x)}
        {S2 = λ m → Dom (mkPainting
                (AddRestrDep (cDeps dc) (cExtraDeps dc)) m)}
        {S3 = λ m → Dom (mkPainting
                (AddRestrDep (cDeps dc) (cExtraDeps dc)) m)}
        {rf0 = λ x → snd (dRestrFrames (cDeps dc)) 0 tt θ x}
        {rfF = λ m → snd (dRestrFrames (cDeps dc)) q Hq ε m}
        {rfG = λ m → snd (dRestrFrames (cDeps dc)) r
                       (le-trans r q k Hr Hq) ω m}
        {F = λ m c → snd (cRestrPaintings dc) q Hq ε m c}
        {G = λ m c → snd (cRestrPaintings dc) r
                       (le-trans r q k Hr Hq) ω m c}
        (snd cohPaintings q Hq r Hr ε ω (snd prevRF 0 tt θ d) (l θ))
        (mkCoh2Frame eDC prevCohFrames q Hq r Hr ε ω θ d))

-- The cohFrames of the next level (Rocq's mkCohFrames) -------------------------

mkCohFrames : {p k : ℕ} {dc : DepsCohs p k}
              (eDC : DepsCohsExtension p k dc)
              (cohPaintings : mkCohPaintingTypes eDC)
              → mkCohFrameTypes (mkExtraDeps eDC) (mkRestrPaintings eDC)
mkCohFrames {zero} eDC cohPaintings = tt , λ q Hq r Hr ε ω d → refl
mkCohFrames {suc p} {k} {dc} eDC cohPaintings =
  prev ,
  λ q Hq r Hr ε ω d →
    Σ≡ (snd prev (suc q) Hq (suc r) Hr ε ω (fst d))
       (mkCohLayer eDC cohPaintings prev q Hq r Hr ε ω (fst d) (snd d))
  where
  prev = mkCohFrames (AddCohDep dc eDC) (fst cohPaintings)

-- The DepsCohs2 class -----------------------------------------------------------

record DepsCohs2 (p k : ℕ) : Set₁ where
  no-eta-equality; pattern
  constructor depsCohs2
  field
    c2DepsCohs : DepsCohs p k
    c2ExtraDepsCohs : DepsCohsExtension p k c2DepsCohs
    c2CohPaintings : mkCohPaintingTypes c2ExtraDepsCohs
open DepsCohs2 public

π₁C2 : {p k : ℕ} → DepsCohs2 (suc p) k → DepsCohs2 p (suc k)
π₁C2 dc2 = depsCohs2 (π₁C (c2DepsCohs dc2))
                     (AddCohDep (c2DepsCohs dc2) (c2ExtraDepsCohs dc2))
                     (fst (c2CohPaintings dc2))

mkDepsCohs : {p k : ℕ} (dc2 : DepsCohs2 p k) → DepsCohs (suc p) k
mkDepsCohs dc2 =
  depsCohs (mkDepsRestr (c2DepsCohs dc2))
           (mkExtraDeps (c2ExtraDepsCohs dc2))
           (mkRestrPaintings (c2ExtraDepsCohs dc2))
           (mkCohFrames (c2ExtraDepsCohs dc2) (c2CohPaintings dc2))

data DepsCohs2Extension : (p k : ℕ) → DepsCohs2 p k → Set₁ where
  TopCoh2Dep : {p : ℕ} {dc2 : DepsCohs2 p 0}
    (E : Dom (mkFrame (mkDepsRestr (mkDepsCohs dc2))) → HSet₀)
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

-- The painting coherence (Rocq's mkCohPainting).  With Π-layers the
-- r = 0 case is refl (Rocq needed nth_lmap); the r,q ≥ 1 case is a
-- dependent Σ-path whose components are the *same* mkCohLayer proof
-- term that mkCohFrames stored — consumed definitionally.

mkCohPainting : {p k : ℕ} {dc2 : DepsCohs2 p k}
                (eDC2 : DepsCohs2Extension p k dc2)
                → mkCohPaintingType (mkExtraCohs eDC2)
mkCohPainting eDC2 q Hq zero Hr ε ω d (l , c) = refl
mkCohPainting eDC2 zero Hq (suc r) () ε ω d c
mkCohPainting (TopCoh2Dep E) (suc q) () (suc r) Hr ε ω d c
mkCohPainting (AddCoh2Dep dc2 eDC2) (suc q) Hq (suc r) Hr ε ω d (l , c) =
  Σ≡dep {P = λ x → Dom (mkLayer _ _
                (dFrames (cDeps (c2DepsCohs dc2)))
                (dPaintings (cDeps (c2DepsCohs dc2)))
                (fst (dRestrFrames (cDeps (c2DepsCohs dc2))))
                (snd (dRestrFrames (cDeps (c2DepsCohs dc2)))) x)}
        {Q = λ z → Dom (mkPainting (cExtraDeps (c2DepsCohs dc2)) z)}
        (snd prev (suc q) Hq (suc r) Hr ε ω d)
        (mkCohLayer (c2ExtraDepsCohs dc2) (c2CohPaintings dc2) prev
          q Hq r Hr ε ω d l)
        (mkCohPainting eDC2 q Hq r Hr ε ω (d , l) c)
  where
  prev = mkCohFrames (AddCohDep (c2DepsCohs dc2) (c2ExtraDepsCohs dc2))
                     (fst (c2CohPaintings dc2))

mkCohPaintings : {p k : ℕ} {dc2 : DepsCohs2 p k}
                 (eDC2 : DepsCohs2Extension p k dc2)
                 → mkCohPaintingTypes (mkExtraCohs eDC2)
mkCohPaintings {zero} eDC2 = tt , mkCohPainting eDC2
mkCohPaintings {suc p} {k} {dc2} eDC2 =
  mkCohPaintings (AddCoh2Dep dc2 eDC2) , mkCohPainting eDC2

-- νSetData and the tower (Rocq's νSetData / νSet / νSetAt / νSetFrom) -----------

record νSetData (p : ℕ) : Set₁ where
  field
    sFrames : mkFrameTypes p 0
    sPaintings : mkPaintingTypes p 0 sFrames
    sRestrFrames : mkRestrFrameTypes p 0 sFrames sPaintings
    sRestrPaintings :
      (E : Dom (mkFrame (depsRestr sFrames sPaintings sRestrFrames))
           → HSet₀)
      → mkRestrPaintingTypes
          {deps = depsRestr sFrames sPaintings sRestrFrames}
          (TopRestrDep E)
    sCohFrames :
      (E : Dom (mkFrame (depsRestr sFrames sPaintings sRestrFrames))
           → HSet₀)
      → mkCohFrameTypes (TopRestrDep E) (sRestrPaintings E)
    sCohPaintings :
      (E : Dom (mkFrame (depsRestr sFrames sPaintings sRestrFrames))
           → HSet₀)
      (E' : Dom (mkFrame (mkDepsRestr
              (depsCohs (depsRestr sFrames sPaintings sRestrFrames)
                (TopRestrDep E) (sRestrPaintings E) (sCohFrames E))))
            → HSet₀)
      → mkCohPaintingTypes
          {dc = depsCohs (depsRestr sFrames sPaintings sRestrFrames)
                  (TopRestrDep E) (sRestrPaintings E) (sCohFrames E)}
          (TopCohDep E')
open νSetData public

mkνSetData : {p : ℕ} (C : νSetData p)
             (E : Dom (mkFrame (depsRestr (sFrames C) (sPaintings C)
                                          (sRestrFrames C))) → HSet₀)
             → νSetData (suc p)
mkνSetData {p} C E = record
  { sFrames = mkFramesD deps0
  ; sPaintings = mkPaintings
      (TopRestrDep {deps = depsRestr (sFrames C) (sPaintings C)
                             (sRestrFrames C)} E)
  ; sRestrFrames = mkRestrFramesC dcE
  ; sRestrPaintings = λ E' → mkRestrPaintings {dc = dcE} (TopCohDep E')
  ; sCohFrames = λ E' → mkCohFrames {dc = dcE} (TopCohDep E')
                          (sCohPaintings C E E')
  ; sCohPaintings = λ E' E'' → mkCohPaintings
      {dc2 = depsCohs2 dcE (TopCohDep E') (sCohPaintings C E E')}
      (TopCoh2Dep E'')
  }
  where
  deps0 : DepsRestr p 0
  deps0 = depsRestr (sFrames C) (sPaintings C) (sRestrFrames C)
  dcE : DepsCohs p 0
  dcE = depsCohs deps0 (TopRestrDep E) (sRestrPaintings C E)
                 (sCohFrames C E)

record νSetStruct (p : ℕ) : Set₂ where
  field
    prefix : Set₁
    struct : prefix → νSetData p
open νSetStruct public

mkPrefix : (p : ℕ) (C : νSetStruct p) → Set₁
mkPrefix p C =
  Σ[ D ∈ prefix C ]
    (Dom (mkFrame (depsRestr (sFrames (struct C D))
                             (sPaintings (struct C D))
                             (sRestrFrames (struct C D)))) → HSet₀)

mkνSet0 : νSetStruct 0
mkνSet0 = record
  { prefix = Unit*
  ; struct = λ _ → record
      { sFrames = tt* ; sPaintings = tt* ; sRestrFrames = tt
      ; sRestrPaintings = λ E → tt
      ; sCohFrames = λ E → tt
      ; sCohPaintings = λ E E' → tt
      }
  }

mkνSet : {p : ℕ} (C : νSetStruct p) → νSetStruct (suc p)
mkνSet {p} C = record
  { prefix = mkPrefix p C
  ; struct = λ D → mkνSetData (struct C (fst D)) (snd D)
  }

νSetAt : (n : ℕ) → νSetStruct n
νSetAt zero    = mkνSet0
νSetAt (suc n) = mkνSet (νSetAt n)

record νSetFrom (n : ℕ) (X : prefix (νSetAt n)) : Set₁ where
  coinductive
  field
    this : Dom (mkFrame (depsRestr (sFrames (struct (νSetAt n) X))
                                   (sPaintings (struct (νSetAt n) X))
                                   (sRestrFrames (struct (νSetAt n) X))))
           → HSet₀
    next : νSetFrom (suc n) (X , this)
open νSetFrom public

νSets : Set₁
νSets = νSetFrom 0 tt*
