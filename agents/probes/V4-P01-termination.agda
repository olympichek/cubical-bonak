------------------------------------------------------------------------
-- Termination probe for the fillers-only νSet block.
--
-- `FunPre` is the cycle obtained from the fillers-only tower by omitting
-- the dimension column: seven members, ten calls, relative indices, a
-- no-eta prefix, and all results erased to `Box`.
-- It reproduces the rejection exactly — remove its `{-# TERMINATING #-}`
-- to see it, and delete any single one of its ten calls to see the whole
-- block be accepted.
--
-- `IndPre` is the same ten calls with one change: the prefix is a
-- length-indexed inductive family instead of a type defined by recursion
-- on ℕ. It is ACCEPTED. So the checker can follow this cycle when the
-- prefix's length is a constructor index it can read, and cannot when
-- the length only appears as the argument of a recursive type former —
-- which is the fillers-only tower's situation. In the corresponding
-- block without an explicit dimension column, changing Pre to an
-- inductive family is necessary but not sufficient, and it costs the
-- reduction of `frame` at a variable prefix plus a Cubical
-- UnsupportedIndexedMatch.
------------------------------------------------------------------------

{-# OPTIONS --rewriting --termination-depth=2 -WnoUnsupportedIndexedMatch #-}

module agents.probes.V4-P01-termination where

open import Bonak.Prelude
open import Bonak.NatRew

data Box : Set₁ where
  box  : Box
  node : Box → Box → Box

------------------------------------------------------------------------
-- The prefix as a type defined by recursion — the tower's situation.
------------------------------------------------------------------------

module FunPre where

  record Snoc (A : Set₁) (B : A → Set₁) : Set₁ where
    no-eta-equality; pattern
    constructor _∷_
    field
      pre : A
      fil : B pre
  open Snoc public

  Pre : ℕ → Set₁
  Fil : (p k : ℕ) (D : Pre (p + k)) → Set₁

  Pre zero    = Unit*
  Pre (suc n) = Snoc (Pre n) (Fil n 0)

  Fil p k D = Unit*

  frame        : (p k : ℕ) (D : Pre (p + k)) → Box
  layer        : (p k : ℕ) (D : Pre (p + k)) (E : Fil (p + k) 0 D) → Box
  restr-frame  : (p k : ℕ) (D : Pre (p + k)) (E : Fil (p + k) 0 D) → Box
  restr-layer  : (p k : ℕ) (D : Pre (p + k)) (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁)) → Box
  coh-frame    : (p k : ℕ) (D : Pre (p + k)) (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁)) → Box
  coh-layer    : (p k : ℕ) (D : Pre (p + k)) (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁))
                 (E₃ : Fil (suc (suc (p + k))) 0 ((D ∷ E₁) ∷ E₂)) → Box
  coh-painting : (p k : ℕ) (D : Pre (p + k)) (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁))
                 (E  : Fil (suc (suc (p + k))) 0 ((D ∷ E₁) ∷ E₂)) → Box

  -- Remove this pragma to reproduce the rejection.
  {-# TERMINATING #-}
  frame zero    k D       = box
  frame (suc p) k (D ∷ E) = node (frame p (suc k) (D ∷ E)) (layer p k D E)

  layer p k D E = restr-frame p k D E

  restr-frame zero    k D        E = box
  restr-frame (suc p) k (D ∷ E₀) E = restr-layer p k D E₀ E

  restr-layer p k D E₁ E₂ = coh-frame p k D E₁ E₂

  coh-frame zero    k D        E₁ E₂ = box
  coh-frame (suc p) k (D ∷ E₀) E₁ E₂ = coh-layer p k D E₀ E₁ E₂

  coh-layer p k D E₁ E₂ E₃ =
    node (coh-painting p k D E₁ E₂ E₃) (frame p k D)

  coh-painting p zero    D        E₁ E₂ E = box
  coh-painting p (suc k) (D ∷ E₀) E₁ E₂ E =
    node (coh-layer p k D E₀ E₁ E₂)
         (coh-painting (suc p) k (D ∷ E₀) E₁ E₂ E)

------------------------------------------------------------------------
-- The same ten calls over a length-indexed inductive family: ACCEPTED,
-- with no pragma.
------------------------------------------------------------------------

module IndPre where

  data Pre : ℕ → Set₁
  Fil : (p k : ℕ) (D : Pre (p + k)) → Set₁

  data Pre where
    ⟨⟩  : Pre zero
    _∷_ : {n : ℕ} (D : Pre n) (E : Fil n 0 D) → Pre (suc n)

  Fil p k D = Unit*

  frame        : (p k : ℕ) (D : Pre (p + k)) → Box
  layer        : (p k : ℕ) (D : Pre (p + k)) (E : Fil (p + k) 0 D) → Box
  restr-frame  : (p k : ℕ) (D : Pre (p + k)) (E : Fil (p + k) 0 D) → Box
  restr-layer  : (p k : ℕ) (D : Pre (p + k)) (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁)) → Box
  coh-frame    : (p k : ℕ) (D : Pre (p + k)) (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁)) → Box
  coh-layer    : (p k : ℕ) (D : Pre (p + k)) (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁))
                 (E₃ : Fil (suc (suc (p + k))) 0 ((D ∷ E₁) ∷ E₂)) → Box
  coh-painting : (p k : ℕ) (D : Pre (p + k)) (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁))
                 (E  : Fil (suc (suc (p + k))) 0 ((D ∷ E₁) ∷ E₂)) → Box

  frame zero    k D       = box
  frame (suc p) k (D ∷ E) = node (frame p (suc k) (D ∷ E)) (layer p k D E)

  layer p k D E = restr-frame p k D E

  restr-frame zero    k D        E = box
  restr-frame (suc p) k (D ∷ E₀) E = restr-layer p k D E₀ E

  restr-layer p k D E₁ E₂ = coh-frame p k D E₁ E₂

  coh-frame zero    k D        E₁ E₂ = box
  coh-frame (suc p) k (D ∷ E₀) E₁ E₂ = coh-layer p k D E₀ E₁ E₂

  coh-layer p k D E₁ E₂ E₃ =
    node (coh-painting p k D E₁ E₂ E₃) (frame p k D)

  coh-painting p zero    D        E₁ E₂ E = box
  coh-painting p (suc k) (D ∷ E₀) E₁ E₂ E =
    node (coh-layer p k D E₀ E₁ E₂)
         (coh-painting (suc p) k (D ∷ E₀) E₁ E₂ E)
