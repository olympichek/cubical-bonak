{-# OPTIONS --cubical #-}

module agents.probes.SigmaComposition where

open import Agda.Primitive.Cubical
  renaming (primIMin to _∧_; primHComp to hcomp; primComp to comp)
open import Agda.Builtin.Cubical.Path using (PathP; _≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)

Path : (A : Set) → A → A → Set
Path A x y = PathP (λ _ → A) x y

refl : {A : Set} {x : A} → x ≡ x
refl {x = x} i = x

infixr 30 _∙_
_∙_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q i =
  hcomp (λ j → λ { (i = i0) → x ; (i = i1) → q j }) (p i)

fill : {A : Set} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → PathP (λ j → x ≡ q j) p (p ∙ q)
fill {x = x} p q j i =
  hcomp (λ k → λ { (i = i0) → x
                  ; (i = i1) → q (j ∧ k)
                  ; (j = i0) → p i }) (p i)

module _ {A : Set} {P : A → Set} where

  infixr 30 _⊙_
  _⊙_ : {x y z : A} {p : x ≡ y} {q : y ≡ z}
    {u : P x} {v : P y} {w : P z}
    (α : PathP (λ i → P (p i)) u v)
    (β : PathP (λ i → P (q i)) v w)
    → PathP (λ i → P ((p ∙ q) i)) u w
  _⊙_ {p = p} {q = q} {u = u} α β i =
    comp (λ j → P (fill p q j i))
      (λ j → λ { (i = i0) → u ; (i = i1) → β j }) (α i)

  eq_trans_eq_existT_curried : {x y z : A} (p : x ≡ y) (q : y ≡ z)
    {u : P x} {v : P y} {w : P z}
    (α : PathP (λ i → P (p i)) u v)
    (β : PathP (λ i → P (q i)) v w)
    → Path (Path (Σ A P) (x , u) (z , w))
        ((λ i → p i , α i) ∙ (λ i → q i , β i))
        (λ i → (p ∙ q) i , (α ⊙ β) i)
  -- Candidate: composition of pairings computes componentwise.
  -- eq_trans_eq_existT_curried p q α β = refl

  -- This candidate is rejected.
  
  -- error: [UnequalTerms]
  -- The terms
  --   primTransp (λ i → A) i ((λ { (i0 = i0) → p i0 , α i0 }) _ .Σ.fst)
  -- and
  --   x
  -- are not equal at type A
  -- when checking that the expression refl has type
  -- Path (Path (Σ A P) (x , u) (z , w))
  --   ((λ i → p i , α i) ∙ (λ i → q i , β i))
  --   (λ i → (p ∙ q) i , (α ⊙ β) i)
  
  -- The record hcomp generator (defineHCompForFields) uses heterogeneous comp for
  -- every field, including fst, whose type A is fixed. comp transports the bottom
  -- and each side into the final fiber before applying hcomp. For fst, these
  -- transports have the form: primTransp (λ _ → A) r a, with r = i0 or the bottom
  -- and r an interval variable for a side. Since A is abstract and r is not
  -- necessarily i1, they do not reduce to a: constancy alone does not give a
  -- definitional identity rule for transport (regularity).

  -- An explicit filler proves the lemma:
  eq_trans_eq_existT_curried {x = x} p q {u = u} α β m i =
    hcomp (λ j → λ
      { (i = i0) → x , u
      ; (i = i1) → q j , β j
      ; (m = i1) → fill p q j i
        , comp (λ k → P (fill p q (j ∧ k) i))
            (λ k → λ { (i = i0) → u
                     ; (i = i1) → β (j ∧ k)
                     ; (j = i0) → α i }) (α i) })
      (p i , α i)
