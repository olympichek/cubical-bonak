------------------------------------------------------------------------
-- probes.V4-P04-depth — can --termination-depth rescue fuel variant
-- (a)?
--
-- V4-P03 shows that conversion forces the fuel discipline into variant
-- (a) of V4-REPORT.md's fuel section: one fuel variable per member,
-- every higher-dimensional occurrence written suc^j of it.  (a) was
-- rejected because the statement-borne calls — the point, layer and
-- restriction occurrences in a member's own statement, which reappear
-- in bodies as solved implicit arguments — carry fuels ABOVE the
-- member's own, by up to three constructors.  Rejected at the file's
-- --termination-depth=2; higher depths track bounded increases, and
-- were never tried on (a).
--
-- This probe decides that axis.  `UpCalls` is V4-P02's ACCEPTED
-- `FuelPre` model — seven members, the ten loop calls, the fuel
-- column with e : n ≡ p + k — plus one explicit call per
-- statement-borne occurrence of the real variant-(a) signatures, at
-- its real fuel offset (frame@+1..+3, layer@+1/+2, restr-frame@+1/+2,
-- coh-frame@+1, restr-layer@+1), lifted into the fuel equation with
-- `cong suc`.  No TERMINATING pragma: the verdict at
-- --termination-depth=N is the answer, and the OPTIONS pragma below is
-- where N is set (a file pragma overrides the command line).
--
-- VERDICT: rejected at depth 1, 2 and 3; ACCEPTED at depth 4 and
-- above.  Edit the pragma to reproduce.  On the real tower the
-- threshold is 3 (Bonak.νSet): the model's explicit up-calls slightly
-- overapproximate the solved-implicit calls the checker actually sees.
------------------------------------------------------------------------

{-# OPTIONS --rewriting --termination-depth=4 #-}

module probes.V4-P04-depth where

open import Bonak.Prelude
open import Bonak.NatRew

data Box : Set₁ where
  box  : Box
  node : Box → Box → Box

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

congS : {m n : ℕ} → m ≡ n → suc m ≡ suc n
congS = cong suc

module UpCalls where

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

  -- layer's statement: the point lives one dimension up (frame@+1).
  layer n p k e D E =
    node (restr-frame n p k e D E)
         (frame (suc n) p (suc k) (congS e) (D ∷ E))

  -- restr-frame's statement: input point frame@+1, result frame@0.
  restr-frame n       zero    k e D        E = box
  restr-frame (suc n) (suc p) k e (D ∷ E₀) E =
    node (restr-layer n p k (injSuc e) D E₀ E)
   (node (frame (suc (suc n)) (suc p) (suc k) (congS e) ((D ∷ E₀) ∷ E))
         (frame (suc n) (suc p) k e (D ∷ E₀)))
  restr-frame zero    (suc p) k e D        E = ⊥-elim (znots e)

  -- restr-layer's statement: frame@+2 (point), layer@+1 (layer arg),
  -- layer@0 (result), restr-frame@+1 (the result's index).
  restr-layer n p k e D E₁ E₂ =
    node (coh-frame n p k e D E₁ E₂)
   (node (frame (suc (suc n)) p (suc (suc k)) (congS (congS e))
            ((D ∷ E₁) ∷ E₂))
   (node (layer (suc n) p (suc k) (congS e) (D ∷ E₁) E₂)
   (node (layer n p k e D E₁)
         (restr-frame (suc n) p (suc k) (congS e) (D ∷ E₁) E₂))))

  -- coh-frame's statement: frame@+2 (point), restr-frame@+1 (inner),
  -- restr-frame@0 (outer sides).
  coh-frame n       zero    k e D        E₁ E₂ = box
  coh-frame (suc n) (suc p) k e (D ∷ E₀) E₁ E₂ =
    node (coh-layer n p k (injSuc e) D E₀ E₁ E₂)
   (node (frame (suc (suc (suc n))) (suc p) (suc (suc k))
            (congS (congS e)) (((D ∷ E₀) ∷ E₁) ∷ E₂))
   (node (restr-frame (suc (suc n)) (suc p) (suc k) (congS e)
            ((D ∷ E₀) ∷ E₁) E₂)
         (restr-frame (suc n) (suc p) k e (D ∷ E₀) E₁)))
  coh-frame zero    (suc p) k e D        E₁ E₂ = ⊥-elim (znots e)

  -- coh-layer's statement: frame@+3 (point), layer@+2 (layer arg),
  -- layer@0 (subst motive), coh-frame@+1 (the subst's path),
  -- restr-layer@+1/@0 (the two sides), restr-frame@+2 (intermediate
  -- point) — plus the loop's own frame@0 (the isSet premise) and the
  -- coh-painting premise.
  coh-layer n p k e D E₁ E₂ E₃ =
    node (coh-painting n p k e D E₁ E₂ E₃)
   (node (frame n p k e D)
   (node (frame (suc (suc (suc n))) p (suc (suc (suc k)))
            (congS (congS (congS e))) (((D ∷ E₁) ∷ E₂) ∷ E₃))
   (node (layer (suc (suc n)) p (suc (suc k)) (congS (congS e))
            ((D ∷ E₁) ∷ E₂) E₃)
   (node (layer n p k e D E₁)
   (node (coh-frame (suc n) p (suc k) (congS e) (D ∷ E₁) E₂ E₃)
   (node (restr-layer n p k e D E₁ E₂)
   (node (restr-layer (suc n) p (suc k) (congS e) (D ∷ E₁) E₂ E₃)
         (restr-frame (suc (suc n)) p (suc (suc k)) (congS (congS e))
            ((D ∷ E₁) ∷ E₂) E₃))))))))

  -- coh-painting's statement: frame@+2 (point), coh-frame@0 (the
  -- subst's path), restr-frame@+1 (intermediate point).
  coh-painting n       p zero    e D        E₁ E₂ E = box
  coh-painting (suc n) p (suc k) e (D ∷ E₀) E₁ E₂ E =
    node (coh-layer n p k (injSuc e) D E₀ E₁ E₂)
   (node (coh-painting (suc n) (suc p) k e (D ∷ E₀) E₁ E₂ E)
   (node (frame (suc (suc (suc n))) p (suc (suc (suc k)))
            (congS (congS e)) (((D ∷ E₀) ∷ E₁) ∷ E₂))
   (node (coh-frame (suc n) p (suc k) e (D ∷ E₀) E₁ E₂)
         (restr-frame (suc (suc n)) p (suc (suc k)) (congS e)
            ((D ∷ E₀) ∷ E₁) E₂))))
  coh-painting zero    p (suc k) e D        E₁ E₂ E = ⊥-elim (znots e)
