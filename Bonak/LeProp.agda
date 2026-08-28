------------------------------------------------------------------------
-- Bonak.LeProp — the recursive ≤ on ℕ (mirroring Rocq's LeSProp.v)
-- and the recursive equality EqN.
--
-- Design (agents/probes/P01-le-transport.agda): Prop-valued ≤ breaks Cubical
-- Agda's transport-clause generation for indexed matches
-- (CannotGenerateTransportClause), so ≤ is Set-valued — recursive into
-- η-⊤ / ⊥ — and *all proof arguments throughout the development are
-- irrelevant* (.), which restores SProp-like definitional irrelevance
-- across neutral proofs (P01 gate 4).
--
-- With the recursive definition, `suc n ≤ suc m` *reduces* to `n ≤ m`,
-- so Rocq's ⇓/⇑ (lower/raise both) are definitional identities and are
-- not needed at all.
------------------------------------------------------------------------

module Bonak.LeProp where

open import Bonak.Prelude using (ℕ; zero; suc; ⊤; tt)

data ⊥ : Set where

exfalso : {ℓ : _} {A : Set ℓ} → ⊥ → A
exfalso ()

infix 4 _≤_
_≤_ : ℕ → ℕ → Set
zero  ≤ m     = ⊤
suc n ≤ zero  = ⊥
suc n ≤ suc m = n ≤ m

leR-refl : {n : ℕ} → n ≤ n
leR-refl {zero}  = tt
leR-refl {suc n} = leR-refl {n}

-- Explicit-argument forms: ≤ is a defined function, so its arguments
-- cannot be recovered by unification from a proof's type — call sites
-- inside the tower use these.

le-trans : (n m p : ℕ) → .(n ≤ m) → .(m ≤ p) → n ≤ p
le-trans zero    m       p       _ _ = tt
le-trans (suc n) zero    p       () _
le-trans (suc n) (suc m) zero    _ ()
le-trans (suc n) (suc m) (suc p) h g = le-trans n m p h g

le-up : (n m : ℕ) → .(n ≤ m) → n ≤ suc m
le-up zero    m       _ = tt
le-up (suc n) zero    ()
le-up (suc n) (suc m) h = le-up n m h

le-down : (n m : ℕ) → .(suc n ≤ m) → n ≤ m
le-down zero    m       _ = tt
le-down (suc n) zero    ()
le-down (suc n) (suc m) h = le-down n m h

infixl 45 _↕_
_↕_ : {n m p : ℕ} → .(n ≤ m) → .(m ≤ p) → n ≤ p
_↕_ {n} {m} {p} h g = le-trans n m p h g

infix 40 ↑_
↑_ : {n m : ℕ} → .(n ≤ m) → n ≤ suc m
↑_ {n} {m} h = le-up n m h

infix 40 ↓_
↓_ : {n m : ℕ} → .(suc n ≤ m) → n ≤ m
↓_ {n} {m} h = le-down n m h

-- EqN, the recursive equality on ℕ, follows the same design.  The
-- dimension columns of Bonak.νSet tie the explicit ℕ argument to the
-- member's indices with a proof of `EqN n m`: `EqN (suc n) (suc m)`
-- REDUCES to `EqN n m`, so one proof is passed down every level of
-- the tower verbatim — no `injSuc`, no transport — and the impossible
-- dimension shapes close with an absurd pattern.

EqN : ℕ → ℕ → Set
EqN zero    zero    = ⊤
EqN zero    (suc m) = ⊥
EqN (suc n) zero    = ⊥
EqN (suc n) (suc m) = EqN n m

eqN-refl : (n : ℕ) → EqN n n
eqN-refl zero    = tt
eqN-refl (suc n) = eqN-refl n
