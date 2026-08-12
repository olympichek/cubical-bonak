-- Probe: what does snd of a composite of pair-paths normalize to?
module probes.P02-sigma-comp where

open import Bonak.Prelude
open import Bonak.RewLemmas
open import Bonak.GpdLemmas

module _ {ℓ ℓ' : Level} {A : Set ℓ} {P : A → Set ℓ'}
         {x y z : A} (p : x ≡ y) (p' : y ≡ z)
         {a : P x} {b : P y} {c : P z}
         (r : PathP (λ i → P (p i)) a b)
         (s : PathP (λ i → P (p' i)) b c) where

  σ1 σ2 : _
  σ1 = λ i → (p i , r i)
  σ2 = λ i → (p' i , s i)

  σ : (x , a) ≡ (z , c)
  σ = _∙_ {A = Σ A P} σ1 σ2

  -- Candidate: the snd of the composite as a comp over the fst-filler.
  -- Deliberately WRONG target type to make Agda print the normal form.
  probe : (λ i → snd (σ i)) ≡ (λ i → snd (σ i))
  probe = refl

  -- Now test whether the fst-line of the composite is the transp-wrapped
  -- composite; print by mismatching against the clean one.
  probe2 : (λ i → fst (σ i)) ≡ (p ∙ p')
  probe2 = refl
