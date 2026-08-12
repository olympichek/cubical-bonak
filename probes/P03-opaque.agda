{-# OPTIONS --cubical --prop --guardedness #-}
module probes.P03-opaque where
open import Bonak.Prelude

opaque
  interleaved mutual
    F : ℕ → Set
    G : ℕ → Set
    F zero = ⊤
    F (suc n) = G n
    G n = F n × ⊤

opaque
  unfolding F
  test : F 1 → ⊤
  test x = tt
