------------------------------------------------------------------------
-- Bonak.NatRew — addition made definitional on both arguments.
--
-- The fillers-only construction stores a prefix of fillers whose LENGTH
-- is p + k, while the tower's steps move p and k in opposite directions
-- (frame decrements p and increments k; painting the other way).  A
-- prefix former must therefore respect all of
--
--   p + zero  ≡ p            (painting's base case: at k = 0 the frame
--                             index IS the prefix length, so the stored
--                             filler applies without a coercion)
--   p + suc k ≡ suc (p + k)  (peeling the top filler)
--   suc p + k ≡ suc (p + k)  (re-splitting the same prefix)
--
-- and no orientation of a recursive addition gives all three: a defined
-- function reduces on one scrutinee at a time.  This is the "reversal
-- obstruction" in its Agda form.  Two rewrite rules remove it.  They are
-- proved, not postulated, so nothing is assumed; what changes is the
-- conversion relation, and with it the flag --rewriting.
--
-- Caveats, worth recording.  Agda's confluence checker does not support
-- --cubical: it warns and skips.  Asking for it anyway
-- (--local-confluence-check) reports the overlap of `+-zero` with the
-- builtin `suc n + m = suc (n + m)` clause as a failure, because the
-- checker does not apply the rule under scrutiny while checking it; the
-- critical pair does join (`suc n + 0` ⇒ `suc n` one way, `suc (n + 0)`
-- ⇒ `suc n` the other), so the rules are confluent by hand and the flag
-- is left off.
------------------------------------------------------------------------

{-# OPTIONS --rewriting #-}

module Bonak.NatRew where

open import Bonak.Prelude using (ℕ; zero; suc; _≡_; refl)
open import Agda.Builtin.Nat public using (_+_)

{-# BUILTIN REWRITE _≡_ #-}

+-zero : (p : ℕ) → p + zero ≡ p
+-zero zero      = refl
+-zero (suc p) i = suc (+-zero p i)

+-suc : (p k : ℕ) → p + suc k ≡ suc (p + k)
+-suc zero    k   = refl
+-suc (suc p) k i = suc (+-suc p k i)

{-# REWRITE +-zero #-}
{-# REWRITE +-suc #-}
