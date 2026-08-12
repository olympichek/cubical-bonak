------------------------------------------------------------------------
-- Bonak.GpdLemmas — the νGpd storey of the Σ-path kit: ports of the
-- remaining SigT.v lemmas (sigT_map_eq, sigT_trans_eq (⊙) and their
-- computation/congruence laws) and of νGpd/Lemmas.v
-- (eq_existT_curried_hex, eq_existT_curried_dep_hex,
-- permutahedral_coherence, rew_coh2Layer, rew_coh2Painting_restr0).
--
-- Statements mirror the Rocq ones 1:1 under the dictionary
--   rew [P] p in u   ↦ subst P p u
--   eq_trans / •     ↦ _∙_
--   f_equal          ↦ cong
--   (= p; q)         ↦ Σ≡ p q          (Bonak.RewLemmas)
--   eq_existT_curried_dep ↦ Σ≡dep      (Bonak.RewLemmas)
--   rew_map          ↦ refl            (definitional in cubical)
--
-- Proofs are cubical rather than J-transcriptions where that is
-- shorter: the key engine is that Σ≡ p q is the PathP-pairing
-- λ i → (p i , toPathP q i), that hcomp on Σ computes componentwise,
-- and that toPathP/fromPathP are inverse up to a path
-- (toPathP-fromPathP / fromPathP-toPathP below).
------------------------------------------------------------------------

module Bonak.GpdLemmas where

open import Bonak.Prelude
open import Bonak.RewLemmas

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  A B C : Set ℓ

------------------------------------------------------------------------
-- Groupoid laws (the ones RewLemmas doesn't have)
------------------------------------------------------------------------

lUnit : {x y : A} (p : x ≡ y) → p ≡ refl ∙ p
lUnit {x = x} p = J (λ _ p → p ≡ refl ∙ p) (rUnit refl) p

rCancel : {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
rCancel {x = x} p = J (λ _ p → p ∙ sym p ≡ refl) (sym (rUnit refl)) p

lCancel : {x y : A} (p : x ≡ y) → sym p ∙ p ≡ refl
lCancel {x = x} p = J (λ _ p → sym p ∙ p ≡ refl) (sym (rUnit refl)) p

-- cong distributes over ∙ — built cubically (not by J) so that its
-- k=0/k=1 faces are literally cong f (p ∙ q) and cong f p ∙ cong f q
-- and, crucially, so that its whiskers by projections stay canonical
-- (fst ∘ cong-∙ (a ,_) is definitionally rUnit refl; see
-- sigT-trans-eq-refl).
cong-∙ : (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z)
         → cong f (p ∙ q) ≡ cong f p ∙ cong f q
cong-∙ f {x = x} p q k j =
  hcomp′ (λ m → λ { (j = i0) → f x
                  ; (j = i1) → f (q m)
                  ; (k = i0) → f (compPath-filler p q m j) })
         (f (p j))

-- J computes on refl, propositionally.
JRefl : {x : A} (P : (y : A) → x ≡ y → Set ℓ') (d : P x refl)
        → J P d refl ≡ d
JRefl P d = transportRefl d

-- Transport in a path type (endpoint on the left).
substInPathL : {x x' y : A} (e : x ≡ x') (q : x ≡ y)
               → subst (λ w → w ≡ y) e q ≡ sym e ∙ q
substInPathL e q =
  J (λ _ e → subst (λ w → w ≡ _) e q ≡ sym e ∙ q)
    (transportRefl q ∙ lUnit q)
    e

------------------------------------------------------------------------
-- toPathP/fromPathP: values on constant lines, and the two round trips
------------------------------------------------------------------------

fromPathPConst : {A : Set ℓ} {x y : A} (r : x ≡ y)
                 → fromPathP {P = λ _ → A} r ≡ transportRefl x ∙ r
fromPathPConst {x = x} r =
  J (λ _ r → fromPathP {P = λ _ → _} r ≡ transportRefl x ∙ r)
    (rUnit (transportRefl x))
    r

toPathPConst : {A : Set ℓ} {x y : A} (q : transport refl x ≡ y)
               → toPathP {P = λ _ → A} q ≡ sym (transportRefl x) ∙ q
toPathPConst {x = x} q = substInPathL (transportRefl x) q

-- The round trips, over an arbitrary path of types E (use them at
-- E := λ i → P (p i), which is definitionally a path in Set).
fromPathP-toPathP : {A B : Set ℓ} (E : A ≡ B) {x : A} {y : B}
                    (q : transport E x ≡ y)
                    → fromPathP {P = λ i → E i} (toPathP {P = λ i → E i} q) ≡ q
fromPathP-toPathP {A = A} E {x} q =
  J (λ _ E → {y : _} (q : transport E x ≡ y)
             → fromPathP {P = λ i → E i} (toPathP {P = λ i → E i} q) ≡ q)
    (λ q → fromPathPConst (toPathP q)
           ∙ cong (transportRefl x ∙_) (toPathPConst q)
           ∙ sym (∙-assoc (transportRefl x) (sym (transportRefl x)) q)
           ∙ cong (_∙ q) (rCancel (transportRefl x))
           ∙ sym (lUnit q))
    E q

toPathP-fromPathP : {A B : Set ℓ} (E : A ≡ B) {x : A} {y : B}
                    (r : PathP (λ i → E i) x y)
                    → toPathP {P = λ i → E i} (fromPathP r) ≡ r
toPathP-fromPathP {A = A} E {x} r =
  J (λ _ E → {y : _} (r : PathP (λ i → E i) x y)
             → toPathP {P = λ i → E i} (fromPathP r) ≡ r)
    (λ r → toPathPConst (fromPathP r)
           ∙ cong (sym (transportRefl x) ∙_) (fromPathPConst r)
           ∙ sym (∙-assoc (sym (transportRefl x)) (transportRefl x) r)
           ∙ cong (_∙ r) (lCancel (transportRefl x))
           ∙ sym (lUnit r))
    E r

-- Transporting a subst-equation along a path between the base paths,
-- seen at the PathP level.
toPathP-over : {A : Set ℓ} {Q : A → Set ℓ'} {x y : A}
               {p1 p2 : x ≡ y} (e : p1 ≡ p2)
               {a : Q x} {b : Q y} (M : subst Q p1 a ≡ b)
               → PathP (λ k → PathP (λ i → Q (e k i)) a b)
                       (toPathP {P = λ i → Q (p1 i)} M)
                       (toPathP {P = λ i → Q (p2 i)}
                                (subst (λ p → subst Q p a ≡ b) e M))
toPathP-over {Q = Q} {p1 = p1} e {a} {b} M =
  J (λ p2 e → PathP (λ k → PathP (λ i → Q (e k i)) a b)
              (toPathP {P = λ i → Q (p1 i)} M)
              (toPathP {P = λ i → Q (p2 i)} (subst (λ p → subst Q p a ≡ b) e M)))
    (cong (toPathP {P = λ i → Q (p1 i)}) (sym (transportRefl M)))
    e

------------------------------------------------------------------------
-- The Σ-path operations: sigT_map_eq and sigT_trans_eq (⊙)
------------------------------------------------------------------------

-- Rocq's projT2_eq: the second projection of a Σ-path, in subst form.
Σ≡-snd : {P : A → Set ℓ'} {u v : Σ A P} (σ : u ≡ v)
         → subst P (cong fst σ) (snd u) ≡ snd v
Σ≡-snd {P = P} σ = fromPathP (λ i → snd (σ i))

-- sigT_map_eq: mapping a fiberwise function over a Σ-path.
sigT-map-eq : {A : Set ℓ} {B : Set ℓ'} {P : A → Set ℓ''} {Q : B → Set ℓ'''}
              {f : A → B} (g : (a : A) → P a → Q (f a))
              {x y : A} {u : P x} {v : P y}
              {p : x ≡ y} (q : subst P p u ≡ v)
              → subst Q (cong f p) (g x u) ≡ g y v
sigT-map-eq {P = P} {Q = Q} {f = f} g {p = p} q =
  fromPathP {P = λ i → Q (f (p i))}
            (λ i → g (p i) (toPathP {P = λ i → P (p i)} q i))

-- sigT_trans_eq: composition of subst-equations over composable base
-- paths — the second projection of the composite Σ-path, re-indexed
-- along cong-∙ fst (fst of an hcomp in Σ only computes to the
-- composite of the fst's up to transp-noise, so this is a subst, not
-- a definitional identification).
sigT-trans-eq : {A : Set ℓ} (P : A → Set ℓ') {x y z : A}
                {u : P x} {v : P y} {w : P z}
                {p : x ≡ y} (q : subst P p u ≡ v)
                {p' : y ≡ z} (q' : subst P p' v ≡ w)
                → subst P (p ∙ p') u ≡ w
sigT-trans-eq P {u = u} {w = w} {p = p} q {p' = p'} q' =
  subst (λ e → subst P e u ≡ w)
        (cong-∙ fst (Σ≡ p q) (Σ≡ p' q'))
        (Σ≡-snd {P = P} (Σ≡ p q ∙ Σ≡ p' q'))

infixl 65 _⊙_

_⊙_ : {A : Set ℓ} {P : A → Set ℓ'} {x y z : A}
      {u : P x} {v : P y} {w : P z}
      {p : x ≡ y} (q : subst P p u ≡ v)
      {p' : y ≡ z} (q' : subst P p' v ≡ w)
      → subst P (p ∙ p') u ≡ w
_⊙_ {P = P} q q' = sigT-trans-eq P q q'

------------------------------------------------------------------------
-- η for Σ-paths, and the two decomposition laws
-- (f_equal_eq_existT_curried, eq_trans_eq_existT_curried)
------------------------------------------------------------------------

Σ≡η : {P : A → Set ℓ'} {u v : Σ A P} (σ : u ≡ v)
      → σ ≡ Σ≡ (cong fst σ) (Σ≡-snd σ)
Σ≡η {P = P} σ k i =
  fst (σ i) ,
  sym (toPathP-fromPathP (λ i → P (fst (σ i))) (λ i → snd (σ i))) k i

-- f_equal_eq_existT_curried
cong-Σ≡ : {A : Set ℓ} {B : Set ℓ'} {P : A → Set ℓ''} {Q : B → Set ℓ'''}
          (f : A → B) (g : (a : A) → P a → Q (f a))
          {x y : A} {u : P x} {v : P y}
          (p : x ≡ y) (q : subst P p u ≡ v)
          → cong {B = λ _ → Σ B Q} (λ z → (f (fst z) , g (fst z) (snd z)))
                 (Σ≡ {P = P} p q)
            ≡ Σ≡ {P = Q} (cong f p) (sigT-map-eq {P = P} {Q = Q} {f = f} g q)
cong-Σ≡ {P = P} {Q = Q} f g p q k i =
  f (p i) ,
  sym (toPathP-fromPathP (λ i → Q (f (p i)))
        (λ i → g (p i) (toPathP {P = λ i → P (p i)} q i))) k i

-- eq_existT_curried_eq: Σ≡ is a congruence in (p, q).
Σ≡-cong2 : {A : Set ℓ} {P : A → Set ℓ'} {x y : A} {u : P x} {v : P y}
           {p p' : x ≡ y}
           {q : subst P p u ≡ v} {q' : subst P p' u ≡ v}
           (Hp : p ≡ p')
           (Hq : subst (λ r → subst P r u ≡ v) Hp q ≡ q')
           → Σ≡ {P = P} p q ≡ Σ≡ {P = P} p' q'
Σ≡-cong2 {P = P} {u = u} {v = v} {p = p} {q = q} Hp Hq k =
  Σ≡ (Hp k) (toPathP {P = λ k → subst P (Hp k) u ≡ v} Hq k)

-- eq_trans_eq_existT_curried
∙-Σ≡ : {A : Set ℓ} {P : A → Set ℓ'} {x y z : A}
       {u : P x} {v : P y} {w : P z}
       (p : x ≡ y) (q : subst P p u ≡ v)
       (p' : y ≡ z) (q' : subst P p' v ≡ w)
       → Σ≡ {P = P} p q ∙ Σ≡ {P = P} p' q'
         ≡ Σ≡ {P = P} (p ∙ p') (_⊙_ {P = P} q q')
∙-Σ≡ {P = P} p q p' q' =
  Σ≡η {P = P} (Σ≡ {P = P} p q ∙ Σ≡ {P = P} p' q')
  ∙ Σ≡-cong2 {P = P}
      {q = Σ≡-snd {P = P} (Σ≡ {P = P} p q ∙ Σ≡ {P = P} p' q')}
      {q' = _⊙_ {P = P} q q'}
      (cong-∙ fst (Σ≡ {P = P} p q) (Σ≡ {P = P} p' q'))
      refl
