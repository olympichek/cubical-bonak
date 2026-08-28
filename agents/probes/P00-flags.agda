{-# OPTIONS --cubical --prop --guardedness #-}

-- Can one module combine the three flags the library enables?
-- (a) --cubical: cubical primitives
-- (b) --prop: leR : ℕ → ℕ → Prop with definitional proof irrelevance
-- (c) --guardedness: coinductive record for νSetFrom
-- Each gate is annotated PASS/FAIL after running.

module agents.probes.P00-flags where

open import Agda.Primitive
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Primitive.Cubical
  renaming (primTransp to transp; primIMin to _∧_; primIMax to _∨_;
            primINeg to ~_)
open import Agda.Builtin.Cubical.Path using (PathP; _≡_)

refl : {ℓ : Level} {A : Set ℓ} {x : A} → x ≡ x
refl {x = x} i = x

-- Gate 1: Prop universe usable at all under --cubical.
data ⊥ : Prop where
record ⊤ : Prop where
  constructor tt

-- Gate 2: recursive Prop-valued leR.
leR : ℕ → ℕ → Prop
leR zero    m       = ⊤
leR (suc n) zero    = ⊥
leR (suc n) (suc m) = leR n m

-- Gate 3: definitional irrelevance across neutral proofs — the
-- load-bearing property. Two abstract proofs of the same leR must be
-- interchangeable in a relevant position (here: an index of a family).
module _ (F : (q k : ℕ) → leR q k → Set) where
  irr-in-index : (q k : ℕ) (h g : leR q k) → F q k h ≡ F q k g
  irr-in-index q k h g = refl

-- Gate 4: leR-composites typecheck (the ↕ / ↑ / ⇓ / ⇑ kit).
leR-trans : (n m p : ℕ) → leR n m → leR m p → leR n p
leR-trans zero    m       p       _ _ = tt
leR-trans (suc n) zero    p       h g = absurd h
  where absurd : {A : Prop} → ⊥ → A
        absurd ()
leR-trans (suc n) (suc m) zero    h g = absurd g
  where absurd : {A : Prop} → ⊥ → A
        absurd ()
leR-trans (suc n) (suc m) (suc p) h g = leR-trans n m p h g

-- Gate 5: coinductive record under --cubical --guardedness.
record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

zeros : Stream ℕ
zeros .head = 0
zeros .tail = zeros

-- Gate 6: transport along a path of Prop-indexed families does not
-- get stuck on the Prop argument (transp on a constant-in-Prop line).
module _ (A : ℕ → Set) where
  shift : (q k : ℕ) (h : leR q k) (P : (q k : ℕ) → leR q k → Set)
          (x : P q k h) (g : leR q k) → P q k g
  shift q k h P x g = x
