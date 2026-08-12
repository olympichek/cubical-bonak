------------------------------------------------------------------------
-- Bonak.LeProp — the recursive ≤ in Prop, mirroring Rocq's LeSProp.v.
--
-- Prop is definitionally proof-irrelevant (validated with --cubical in
-- probes/P00-flags.agda), so bound proofs can be weakened, shifted and
-- composed freely, exactly like Rocq's SProp.
------------------------------------------------------------------------

module Bonak.LeProp where

open import Bonak.Prelude using (ℕ; zero; suc)

data SFalse : Prop where
record STrue : Prop where
  constructor sI

infix 4 _≤_
_≤_ : ℕ → ℕ → Prop
zero  ≤ m     = STrue
suc n ≤ zero  = SFalse
suc n ≤ suc m = n ≤ m

-- Absurdity elimination out of Prop's empty type (one per target sort)
exfalso : {ℓ : _} {A : Set ℓ} → SFalse → A
exfalso ()

exfalsoP : {A : Prop} → SFalse → A
exfalsoP ()

leR-refl : {n : ℕ} → n ≤ n
leR-refl {zero}  = sI
leR-refl {suc n} = leR-refl {n}

leR-O : {n : ℕ} → zero ≤ n
leR-O = sI

leR-O-contra : {n : ℕ} → suc n ≤ zero → SFalse
leR-O-contra h = h

infixl 45 _↕_
_↕_ : {n m p : ℕ} → n ≤ m → m ≤ p → n ≤ p
_↕_ {zero}  {m}     {p}     _ _ = sI
_↕_ {suc n} {zero}  {p}     h _ = exfalsoP h
_↕_ {suc n} {suc m} {zero}  _ g = exfalsoP g
_↕_ {suc n} {suc m} {suc p} h g = _↕_ {n} {m} {p} h g

infix 40 ↑_
↑_ : {n m : ℕ} → n ≤ m → n ≤ suc m
↑_ {zero}  {m}     _ = sI
↑_ {suc n} {zero}  h = exfalsoP h
↑_ {suc n} {suc m} h = ↑_ {n} {m} h

infix 40 ↓_
↓_ : {n m : ℕ} → suc n ≤ m → n ≤ m
↓_ {zero}  {m}     _ = sI
↓_ {suc n} {zero}  h = exfalsoP h
↓_ {suc n} {suc m} h = ↓_ {n} {m} h

-- Lower/raise both sides: definitional identities on _≤_
infix 40 ⇓_
⇓_ : {n m : ℕ} → suc n ≤ suc m → n ≤ m
⇓ h = h

infix 40 ⇑_
⇑_ : {n m : ℕ} → n ≤ m → suc n ≤ suc m
⇑ h = h
