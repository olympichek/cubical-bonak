------------------------------------------------------------------------
-- V4-P00 — can the (p,k) reversal obstruction be dissolved by REWRITE?
--
-- V4's prefix of fillers has length p + k.  Both indices move under the
-- tower's steps (frame decrements p / increments k; painting the other
-- way), so the prefix type must be invariant under BOTH
--
--   suc p + k ≡ suc (p + k)      (frame's re-split)
--   p + suc k ≡ suc (p + k)      (painting's step / the top peel)
--   p + zero  ≡ p                (painting's base: the filler's index)
--
-- and no orientation of a *defined* addition gives all three, because a
-- defined function reduces on one scrutinee at a time.  Two REWRITE
-- rules make all three hold definitionally.  Gates:
--   1. --cubical + --prop + --guardedness + --rewrite coexist;
--   2. the cubical Path type is usable as the REWRITE relation;
--   3. the rules fire under *variable* p and k;
--   4. confluence check passes.
------------------------------------------------------------------------

{-# OPTIONS --rewriting --local-confluence-check #-}

module V4-P00-rewrite where

open import Bonak.Prelude
open import Bonak.LeProp using (_≤_; le-trans; le-up)

open import Agda.Builtin.Nat public using (_+_)

{-# BUILTIN REWRITE _≡_ #-}

+-zero : (p : ℕ) → p + zero ≡ p
+-zero zero    = refl
+-zero (suc p) i = suc (+-zero p i)

+-suc : (p k : ℕ) → p + suc k ≡ suc (p + k)
+-suc zero    k = refl
+-suc (suc p) k i = suc (+-suc p k i)

{-# REWRITE +-zero #-}
{-# REWRITE +-suc #-}

-- Gate 3: all four equations definitional at VARIABLE p, k. -------------

gate-zero : (p : ℕ) → (p + zero) ≡ p
gate-zero p = refl

gate-sucR : (p k : ℕ) → (p + suc k) ≡ suc (p + k)
gate-sucR p k = refl

gate-sucL : (p k : ℕ) → (suc p + k) ≡ suc (p + k)
gate-sucL p k = refl

-- The reversal itself: the two split forms of the same length.
gate-reversal : (p k : ℕ) → (suc p + k) ≡ (p + suc k)
gate-reversal p k = refl

-- Gate 3b: it fires in TYPE positions, which is what the prefix needs.
Pre? : ℕ → Set
Pre? zero    = ⊤
Pre? (suc n) = ℕ × Pre? n

gate-type : (p k : ℕ) → Pre? (suc p + k) ≡ Pre? (p + suc k)
gate-type p k = refl

-- and the peel is definitional at a variable prefix index:
gate-peel : (p k : ℕ) → Pre? (p + suc k) ≡ (ℕ × Pre? (p + k))
gate-peel p k = refl

-- Gate 5: the LeProp bounds are untouched by all this (suc q ≤ suc k
-- still *reduces* to q ≤ k, so V1's bound expressions carry over).
gate-le : (q k : ℕ) → (suc q ≤ suc k) ≡ (q ≤ k)
gate-le q k = refl

-- ... and a q ≤ k proof is accepted verbatim where suc q ≤ suc k is
-- wanted (in the irrelevant positions the tower uses it in): this is
-- what makes V1's bound expressions carry over to V4 unchanged.
consumer : (q k : ℕ) .(H : suc q ≤ suc k) → ℕ
consumer q k H = q

gate-le-transport : (q k : ℕ) .(Hq : q ≤ k) → ℕ
gate-le-transport q k Hq = consumer q k Hq
