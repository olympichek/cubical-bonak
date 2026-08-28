------------------------------------------------------------------------
-- Bonak.NatRew — addition made definitional on both arguments.
--
-- The fillers-only construction stores a prefix of fillers whose length
-- is p + k, while the tower's steps move p and k in opposite directions
-- (frame decrements p and increments k; painting the other way). A
-- prefix former must therefore respect all of
--
-- `p + zero ≡ p`, so at k = 0 the frame index is the prefix length and
-- the stored filler applies without a coercion;
-- `p + suc k ≡ suc (p + k)`, for peeling the top filler; and
-- `suc p + k ≡ suc (p + k)`, for re-splitting the same prefix.
--
-- No orientation of a recursive addition gives all three: a defined
-- function reduces on one scrutinee at a time. Two rewrite rules
-- resolve this mismatch. They are proved, not postulated, so nothing
-- is assumed; what changes is the conversion relation, and with it
-- the flag --rewriting.
--
-- Caveats, worth recording. Agda's confluence checker does not support
-- --cubical: it warns and skips. Asking for it anyway
-- (--local-confluence-check) reports the overlap of `+-zero` with the
-- builtin `suc n + m = suc (n + m)` clause as a failure, because the
-- checker does not apply the rule under scrutiny while checking it;
-- the one critical pair joins by normalization — `suc n + 0` reduces
-- to `suc n` directly or through `suc (n + 0)` — so the flag is left
-- off.
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
