{-# OPTIONS --cubical --prop --guardedness #-}
-- P04: Agda 2.8.0's `unfolding` is BODY-ONLY.  A definition's type
-- signature inside `opaque … unfolding F` still sees F as opaque (this
-- file is EXPECTED TO FAIL).  Consequence for the νGpd port: a tower
-- stage can only be folded if its values are never applied in a
-- signature — mkCohLayer's PathP statement applies cohFrame data in its
-- signature, so folding mkCohFrameType requires first naming every such
-- statement as a definition (Rocq's νGpd.v:692 trick, which thereby
-- gains a second justification in Agda).
module probes.P04-unfold where
open import Bonak.Prelude

opaque
  F : ℕ → Set
  F n = ℕ → ⊤

opaque
  unfolding F

  module M (x : F 0) where
    test : (n : ℕ) → x n ≡ tt
    test n = refl
