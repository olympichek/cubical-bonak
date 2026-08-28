------------------------------------------------------------------------
-- Can an explicit length argument replace the TERMINATING pragma?
--
-- `DimPre` isolates a rejected cycle with seven members, ten calls, and
-- `Pre` defined by recursion on ℕ. It adds two arguments to every
-- member: the prefix length `n : ℕ` and the equation `e : n ≡ p + k`.
-- `n` occurs in no
-- type: it is matched and peeled purely so the termination checker gets
-- a single argument column that never increases and strictly decreases
-- on every descent edge. The equation is what makes the bookkeeping
-- total: `injSuc e` peels it in step with `n`, and it refutes the
-- `n ≡ zero` clauses that the extra match would otherwise leave open.
-- The rewrite rules of Bonak.NatRew keep the equation's type normal
-- (`suc p + k`, `p + suc k` and `suc n` all display as `suc (p + k)` /
-- `suc n`), so `e` is passed along unchanged on the p↔k trading edges
-- and peeled exactly where `n` is.
--
-- No TERMINATING pragma anywhere in this file. The block is accepted at
-- the default termination depth as well: the dimension column alone
-- carries the argument, so termination depth is irrelevant here.
--
-- The scope of that result is set by the erasure: every member here
-- returns `Box`, so the dimension occurs in no type. A tower whose members
-- take points and paths of the frames they build puts the dimension into the
-- types of those arguments, and the column is then pinned: a statement
-- names objects both above and below its own prefix, and one of the two
-- directions stops being expressible from a single dimension variable.
------------------------------------------------------------------------

{-# OPTIONS --rewriting --termination-depth=2 #-}

module agents.probes.V4-P02-dimension where

open import Bonak.Prelude
open import Bonak.NatRew

data Box : Set₁ where
  box  : Box
  node : Box → Box → Box

-- Refuting zero ≡ suc and peeling suc ≡ suc, cubically -------------------

data ⊥ : Set where

⊥-elim : ∀ {ℓ} {A : Set ℓ} → ⊥ → A
⊥-elim ()

IsZero : ℕ → Set
IsZero zero    = ⊤
IsZero (suc _) = ⊥

znots : {m : ℕ} → zero ≡ suc m → ⊥
znots e = subst IsZero e tt

predℕ : ℕ → ℕ
predℕ zero    = zero
predℕ (suc m) = m

injSuc : {m n : ℕ} → suc m ≡ suc n → m ≡ n
injSuc = cong predℕ

------------------------------------------------------------------------
-- FunPre's cycle with the dimension column.
------------------------------------------------------------------------

module DimPre where

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

  frame        : (n p k : ℕ) (e : n ≡ p + k) (D : Pre (p + k)) → Box
  layer        : (n p k : ℕ) (e : n ≡ p + k) (D : Pre (p + k))
                 (E : Fil (p + k) 0 D) → Box
  restr-frame  : (n p k : ℕ) (e : n ≡ p + k) (D : Pre (p + k))
                 (E : Fil (p + k) 0 D) → Box
  restr-layer  : (n p k : ℕ) (e : n ≡ p + k) (D : Pre (p + k))
                 (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁)) → Box
  coh-frame    : (n p k : ℕ) (e : n ≡ p + k) (D : Pre (p + k))
                 (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁)) → Box
  coh-layer    : (n p k : ℕ) (e : n ≡ p + k) (D : Pre (p + k))
                 (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁))
                 (E₃ : Fil (suc (suc (p + k))) 0 ((D ∷ E₁) ∷ E₂)) → Box
  coh-painting : (n p k : ℕ) (e : n ≡ p + k) (D : Pre (p + k))
                 (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁))
                 (E  : Fil (suc (suc (p + k))) 0 ((D ∷ E₁) ∷ E₂)) → Box

  frame n       zero    k e D       = box
  frame (suc n) (suc p) k e (D ∷ E) =
    node (frame (suc n) p (suc k) e (D ∷ E))
         (layer n p k (injSuc e) D E)
  frame zero    (suc p) k e D       = ⊥-elim (znots e)

  layer n p k e D E = restr-frame n p k e D E

  restr-frame n       zero    k e D        E = box
  restr-frame (suc n) (suc p) k e (D ∷ E₀) E =
    restr-layer n p k (injSuc e) D E₀ E
  restr-frame zero    (suc p) k e D        E = ⊥-elim (znots e)

  restr-layer n p k e D E₁ E₂ = coh-frame n p k e D E₁ E₂

  coh-frame n       zero    k e D        E₁ E₂ = box
  coh-frame (suc n) (suc p) k e (D ∷ E₀) E₁ E₂ =
    coh-layer n p k (injSuc e) D E₀ E₁ E₂
  coh-frame zero    (suc p) k e D        E₁ E₂ = ⊥-elim (znots e)

  coh-layer n p k e D E₁ E₂ E₃ =
    node (coh-painting n p k e D E₁ E₂ E₃) (frame n p k e D)

  coh-painting n       p zero    e D        E₁ E₂ E = box
  coh-painting (suc n) p (suc k) e (D ∷ E₀) E₁ E₂ E =
    node (coh-layer n p k (injSuc e) D E₀ E₁ E₂)
         (coh-painting (suc n) (suc p) k e (D ∷ E₀) E₁ E₂ E)
  coh-painting zero    p (suc k) e D        E₁ E₂ E = ⊥-elim (znots e)
