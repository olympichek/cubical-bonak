------------------------------------------------------------------------
-- Bonak.Prelude — self-contained mini cubical prelude.
--
-- Builtin primitives only; provides exactly what the νSet/νGpd mirror
-- needs: paths, transport, funExt, Σ with η, and the h-level kit
-- (isProp/isSet, closure under ⊤, Σ, Π).
------------------------------------------------------------------------

module Bonak.Prelude where

open import Agda.Primitive public
  using (Level; lzero; lsuc; _⊔_; Set)
open import Agda.Primitive.Cubical public
  renaming ( primIMin to _∧_ ; primIMax to _∨_ ; primINeg to ~_
           ; primTransp to transp ; primHComp to hcomp′ )
  using    ( I; i0; i1; Partial; IsOne; itIsOne )
open import Agda.Builtin.Cubical.Path public
  using (PathP; _≡_)
open import Agda.Builtin.Sigma public
  using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit public
  using (⊤; tt)
open import Agda.Builtin.Bool public
  using (Bool; true; false)
open import Agda.Builtin.Nat public
  using (zero; suc) renaming (Nat to ℕ)

private variable
  ℓ ℓ' ℓ'' : Level
  A B C : Set ℓ

-- Σ notation ----------------------------------------------------------

infixr 4 _×_
_×_ : Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)

Σ-syntax : (A : Set ℓ) → (A → Set ℓ') → Set (ℓ ⊔ ℓ')
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- Basic path combinators ------------------------------------------------

refl : {x : A} → x ≡ x
refl {x = x} _ = x

sym : {x y : A} → x ≡ y → y ≡ x
sym p i = p (~ i)

cong : {B : A → Set ℓ'} (f : (a : A) → B a) {x y : A}
       (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
cong f p i = f (p i)

cong₂ : (f : A → B → C) {x y : A} {u v : B}
        → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f p q i = f (p i) (q i)

transport : {A B : Set ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

subst : (P : A → Set ℓ') {x y : A} → x ≡ y → P x → P y
subst P p u = transport (λ i → P (p i)) u

transportRefl : {A : Set ℓ} (x : A) → transport refl x ≡ x
transportRefl {A = A} x i = transp (λ _ → A) i x

substRefl : (P : A → Set ℓ') {x : A} (u : P x) → subst P refl u ≡ u
substRefl P u = transportRefl u

-- Path composition (standard hcomp-based) -------------------------------

infixr 30 _∙_
_∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q i =
  hcomp′ (λ j → λ { (i = i0) → x
                  ; (i = i1) → q j })
         (p i)

-- funExt ----------------------------------------------------------------

funExt : {B : A → Set ℓ'} {f g : (a : A) → B a}
         → ((a : A) → f a ≡ g a) → f ≡ g
funExt h i a = h a i

funExt⁻ : {B : A → Set ℓ'} {f g : (a : A) → B a}
          → f ≡ g → (a : A) → f a ≡ g a
funExt⁻ p a i = p i a

-- h-levels ---------------------------------------------------------------

isProp : Set ℓ → Set ℓ
isProp A = (x y : A) → x ≡ y

isSet : Set ℓ → Set ℓ
isSet A = (x y : A) → isProp (x ≡ y)

isProp→isSet : isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp′ (λ k → λ { (i = i0) → h a a k
                  ; (i = i1) → h a b k
                  ; (j = i0) → h a (p i) k
                  ; (j = i1) → h a (q i) k })
         a

-- PathP ↔ transported path ------------------------------------------------

PathP≡Path : (P : I → Set ℓ) (p : P i0) (q : P i1)
             → PathP P p q ≡ (transport (λ i → P i) p ≡ q)
PathP≡Path P p q i =
  PathP (λ j → P (i ∨ j)) (transp (λ j → P (i ∧ j)) (~ i) p) q

toPathP : {P : I → Set ℓ} {x : P i0} {y : P i1}
          → transport (λ i → P i) x ≡ y → PathP P x y
toPathP {P = P} {x} {y} h = transport (sym (PathP≡Path P x y)) h

isSet→isPropPathP : (P : I → Set ℓ) → isSet (P i1)
                    → (x : P i0) (y : P i1) → isProp (PathP P x y)
isSet→isPropPathP P sP1 x y =
  subst isProp (sym (PathP≡Path P x y)) (sP1 (transport (λ i → P i) x) y)

isProp→PathP : {P : I → Set ℓ} (h : (i : I) → isProp (P i))
               (x : P i0) (y : P i1) → PathP P x y
isProp→PathP {P = P} h x y = toPathP (h i1 (transport (λ i → P i) x) y)

-- Closure of isSet under the type formers the tower uses ------------------

isProp⊤ : isProp ⊤
isProp⊤ _ _ _ = tt

isSet⊤ : isSet ⊤
isSet⊤ = isProp→isSet isProp⊤

isSetΠ : {B : A → Set ℓ'} → ((a : A) → isSet (B a))
         → isSet ((a : A) → B a)
isSetΠ sB f g p q j i a = sB a (f a) (g a) (λ k → p k a) (λ k → q k a) j i

isSetΣ : {B : A → Set ℓ'} → isSet A → ((a : A) → isSet (B a))
         → isSet (Σ A B)
isSetΣ {B = B} sA sB u v p q = λ j i → α j i , β j i
  where
  α : (λ i → fst (p i)) ≡ (λ i → fst (q i))
  α = sA (fst u) (fst v) (λ i → fst (p i)) (λ i → fst (q i))
  β : PathP (λ j → PathP (λ i → B (α j i)) (snd u) (snd v))
            (λ i → snd (p i)) (λ i → snd (q i))
  β = isProp→PathP
        (λ j → isSet→isPropPathP (λ i → B (α j i)) (sB (fst v))
               (snd u) (snd v))
        (λ i → snd (p i)) (λ i → snd (q i))

-- HSet ---------------------------------------------------------------------

record HSet (ℓ : Level) : Set (lsuc ℓ) where
  constructor hset
  field
    Dom : Set ℓ
    isSetDom : isSet Dom
open HSet public

hunit : HSet lzero
hunit = hset ⊤ isSet⊤

hΣ : (A : HSet ℓ) (B : Dom A → HSet ℓ') → HSet (ℓ ⊔ ℓ')
hΣ A B = hset (Σ (Dom A) (λ a → Dom (B a)))
              (isSetΣ (isSetDom A) (λ a → isSetDom (B a)))

hΠ : (A : Set ℓ) (B : A → HSet ℓ') → HSet (ℓ ⊔ ℓ')
hΠ A B = hset ((a : A) → Dom (B a)) (isSetΠ (λ a → isSetDom (B a)))
