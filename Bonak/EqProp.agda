------------------------------------------------------------------------
-- Bonak.EqProp — the recursive equality on ℕ, mirroring Bonak.LeProp.
--
-- The fuel columns of Bonak.νSet tie a fuel variable to a dimension
-- with a proof of `EqN n m`.  Like LeProp's ≤ it is recursive into
-- η-⊤ / ⊥ and used irrelevantly (.) throughout: `EqN (suc n) (suc m)`
-- REDUCES to `EqN n m`, so one proof is passed down every level of the
-- tower verbatim — no `injSuc`, no transport — and the impossible fuel
-- shapes close with an absurd pattern.
------------------------------------------------------------------------

module Bonak.EqProp where

open import Bonak.Prelude using (ℕ; zero; suc; ⊤; tt)
open import Bonak.LeProp using (⊥)

EqN : ℕ → ℕ → Set
EqN zero    zero    = ⊤
EqN zero    (suc m) = ⊥
EqN (suc n) zero    = ⊥
EqN (suc n) (suc m) = EqN n m

eqN-refl : (n : ℕ) → EqN n n
eqN-refl zero    = tt
eqN-refl (suc n) = eqN-refl n
