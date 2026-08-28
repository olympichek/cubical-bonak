{-# OPTIONS --cubical --prop --guardedness #-}

-- P01: which representation of ≤ survives pattern matching on an
-- indexed family (which makes Cubical Agda generate transport
-- clauses)?  Reproduces the CannotGenerateTransportClause error from
-- νSet.agda's mkRestrPainting and tests the alternatives.

module agents.probes.P01-le-transport where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Primitive.Cubical renaming (primTransp to transp)
open import Agda.Builtin.Cubical.Path using (_≡_)

data SFalse : Prop where
record STrue : Prop where
  constructor sI

_≤ᴾ_ : ℕ → ℕ → Prop
zero  ≤ᴾ m     = STrue
suc n ≤ᴾ zero  = SFalse
suc n ≤ᴾ suc m = n ≤ᴾ m

-- Set-valued recursive ≤ (⊤/⊥ with η-unit)
data ⊥ : Set where
record ⊤ : Set where
  constructor tt

_≤ˢ_ : ℕ → ℕ → Set
zero  ≤ˢ m     = ⊤
suc n ≤ˢ zero  = ⊥
suc n ≤ˢ suc m = n ≤ˢ m

-- A minimal indexed family in the shape of DepsCohsExtension
data Fam : (k : ℕ) → Set where
  top : Fam 0
  add : {k : ℕ} → Fam k → Fam (suc k)

-- Gate 1 (expected FAIL, the νSet error): Prop-valued bound argument
-- alongside an indexed match.
-- gate1 : {k : ℕ} (f : Fam k) (q : ℕ) (Hq : (suc q) ≤ᴾ k) → ℕ
-- gate1 (add f) q Hq = q
-- gate1 top q ()

-- Gate 2: Set-valued ⊤/⊥ recursive bound, relevant.
gate2 : {k : ℕ} (f : Fam k) (q : ℕ) (Hq : (suc q) ≤ˢ k) → ℕ
gate2 (add f) q Hq = q
gate2 top q ()

-- Gate 3: Set-valued bound, irrelevant argument — do absurd patterns
-- and conversion-irrelevance work?
gate3 : {k : ℕ} (f : Fam k) (q : ℕ) .(Hq : (suc q) ≤ˢ k) → ℕ
gate3 (add f) q Hq = q
gate3 top q ()

-- Gate 4: irrelevance is definitional across neutral proofs in an
-- index position.
module _ (F : (q k : ℕ) .(h : q ≤ˢ k) → Set) where
  irr : (q k : ℕ) .(h g : q ≤ˢ k) → F q k h ≡ F q k g
  irr q k h g i = F q k h

-- Gate 5: Prop bound argument but NO indexed match in scope — fine
-- (control; this is what P00 validated).
gate5 : (q k : ℕ) (Hq : (suc q) ≤ᴾ k) → ℕ
gate5 q k Hq = q
