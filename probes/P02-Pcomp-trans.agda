-- Probe: the base 2-cells entering ⊙'s definition agree definitionally
-- between the layer level and the component level (fst-projections of
-- Σ-hcomps compute componentwise), for general index paths p, p'.

module probes.P02-Pcomp-trans where

open import Bonak.Prelude
open import Bonak.RewLemmas
open import Bonak.GpdLemmas
open import Bonak.LayerHexBridge

module _ {A' T : Set} {B : A' → T → Set} {x y z : T}
  {p : x ≡ y} {p' : y ≡ z}
  {u : (ω : A') → B ω x} {v : (ω : A') → B ω y} {w : (ω : A') → B ω z}
  (X : subst (λ t → (ω : A') → B ω t) p u ≡ v)
  (Y : subst (λ t → (ω : A') → B ω t) p' v ≡ w)
  (ω : A')
  where

  private
    L : T → Set
    L t = (ω' : A') → B ω' t

  -- the index-path 2-cells of the two ⊙'s
  testS2 : cong-∙ fst (Σ≡ {P = L} {u2 = u} {v2 = v} p X) (Σ≡ {P = L} {u2 = v} {v2 = w} p' Y)
           ≡ cong-∙ fst
               (Σ≡ {P = B ω} {u2 = u ω} {v2 = v ω} p (Πcomp {B = B} {e = p} {f = u} {g = v} X ω))
               (Σ≡ {P = B ω} {u2 = v ω} {v2 = w ω} p'
                 (Πcomp {B = B} {e = p'} {f = v} {g = w} Y ω))
  testS2 = refl

  private
    σL : PathP (λ _ → Σ T L) (x , u) (z , w)
    σL = Σ≡ {P = L} {u2 = u} {v2 = v} p X
         ∙ Σ≡ {P = L} {u2 = v} {v2 = w} p' Y
    σB : PathP (λ _ → Σ T (B ω)) (x , u ω) (z , w ω)
    σB = Σ≡ {P = B ω} {u2 = u ω} {v2 = v ω} p
           (Πcomp {B = B} {e = p} {f = u} {g = v} X ω)
         ∙ Σ≡ {P = B ω} {u2 = v ω} {v2 = w ω} p'
           (Πcomp {B = B} {e = p'} {f = v} {g = w} Y ω)

  -- the fst-lines of the composite Σ-paths
  testFst : PathP (λ _ → PathP (λ _ → T) x z)
              (λ i → fst (σL i)) (λ i → fst (σB i))
  testFst = refl

module _ {A' T : Set} {B : A' → T → Set} {x : T}
  {u v w : (ω : A') → B ω x}
  (X : subst (λ t → (ω : A') → B ω t) refl u ≡ v)
  (Y : subst (λ t → (ω : A') → B ω t) refl v ≡ w)
  (ω : A')
  where

  private
    L : T → Set
    L t = (ω' : A') → B ω' t

  -- ⊙-reflSquare agreement (the closed cube does not see the fibers)
  testSq : ⊙-reflSquare′ {P = L} {u = u} {v = v} {w = w} X Y
           ≡ ⊙-reflSquare′ {P = B ω} {u = u ω} {v = v ω} {w = w ω}
               (Πcomp {B = B} {e = refl} {f = u} {g = v} X ω)
               (Πcomp {B = B} {e = refl} {f = v} {g = w} Y ω)
  testSq = refl
