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

------------------------------------------------------------------------
-- Computation of the operations at refl
-- (sigT_map_eq_refl, sigT_trans_eq_refl)
--
-- NB. Rocq's statements (`sigT_map_eq g (p:=eq_refl) q = f_equal (g x) q`
-- and `sigT_trans_eq (p:=eq_refl) q (p':=eq_refl) q' = eq_trans q q'`)
-- type-check only because `rew eq_refl in u` REDUCES in Rocq; in
-- cubical `subst P refl u` does not, so the ports below carry the
-- transport corrections explicitly (substRefl-conjugations and, for ⊙,
-- the index square refl ≡ refl ∙ refl its construction produces).
------------------------------------------------------------------------

symDistr : {x y z : A} (p : x ≡ y) (q : y ≡ z)
           → sym (p ∙ q) ≡ sym q ∙ sym p
symDistr p q =
  J (λ _ q → sym (p ∙ q) ≡ sym q ∙ sym p)
    (cong sym (sym (rUnit p)) ∙ lUnit (sym p))
    q

sigT-map-eq-refl : {A : Set ℓ} {B : Set ℓ'} {P : A → Set ℓ''} {Q : B → Set ℓ'''}
                   {f : A → B} (g : (a : A) → P a → Q (f a))
                   {x : A} {u v : P x} (q : subst P refl u ≡ v)
                   → sigT-map-eq {P = P} {Q = Q} {f = f} g {p = refl} q
                     ≡ substRefl Q (g x u) ∙ cong (g x) (sym (substRefl P u) ∙ q)
sigT-map-eq-refl {P = P} {Q = Q} g {x = x} {u = u} q =
  fromPathPConst (λ i → g x (toPathP {P = λ _ → P x} q i))
  ∙ cong (λ r → transportRefl (g x u) ∙ cong (g x) r) (toPathPConst q)

-- The 2-path refl ≡ refl ∙ refl produced by ⊙'s construction at
-- p = p' = refl (it normalizes to a closed hcomp-cube in A that does
-- not depend on q, q'; it is merely most convenient to write it with
-- them).
⊙-reflSquare : {A : Set ℓ} {P : A → Set ℓ'} {x : A} {u v w : P x}
               (q : subst P refl u ≡ v) (q' : subst P refl v ≡ w)
               → refl {x = x} ≡ refl ∙ refl
⊙-reflSquare {A = A} {P = P} {x = x} q q' =
  (λ k j → fst (cong-∙ {A = P x} {B = Σ A P} (x ,_)
                       (toPathP {P = λ _ → P x} q)
                       (toPathP {P = λ _ → P x} q') k j))
  ∙ cong-∙ fst (Σ≡ {P = P} refl q) (Σ≡ {P = P} refl q')

sigT-trans-eq-refl : {A : Set ℓ} {P : A → Set ℓ'} {x : A} {u v w : P x}
                     (q : subst P refl u ≡ v) (q' : subst P refl v ≡ w)
                     → _⊙_ {P = P} {p = refl} q {p' = refl} q'
                       ≡ cong (λ e → subst P e u)
                              (sym (⊙-reflSquare {P = P} q q'))
                         ∙ q ∙ sym (substRefl P v) ∙ q'
sigT-trans-eq-refl {A = A} {P = P} {x = x} {u = u} {v = v} {w = w} q q' =
  step1
  ∙ cong (sym cgS₀ ∙_) (step2 ∙ cong (sym cgW₁ ∙_) step345)
  ∙ end
  where
  pair : P x → Σ A P
  pair = (x ,_)

  ψ ψ' : _
  ψ = toPathP {P = λ _ → P x} q
  ψ' = toPathP {P = λ _ → P x} q'

  σ : (x , u) ≡ (x , w)
  σ = Σ≡ {P = P} refl q ∙ Σ≡ {P = P} refl q'

  -- cong-∙ for the pairing map; its left endpoint is cong pair (ψ ∙ ψ')
  -- and its right endpoint is definitionally σ.
  T : cong pair (ψ ∙ ψ') ≡ σ
  T = cong-∙ pair ψ ψ'

  W₁ : refl {x = x} ≡ cong fst σ
  W₁ = λ k j → fst (T k j)

  S₀ : cong fst σ ≡ refl ∙ refl
  S₀ = cong-∙ fst (Σ≡ {P = P} refl q) (Σ≡ {P = P} refl q')

  h : x ≡ x → P x
  h e = subst P e u

  cgS₀ : subst P (cong fst σ) u ≡ subst P (refl ∙ refl) u
  cgS₀ = λ k → h (S₀ k)

  cgW₁ : subst P refl u ≡ subst P (cong fst σ) u
  cgW₁ = λ k → h (W₁ k)

  X : subst P (cong fst σ) u ≡ w
  X = Σ≡-snd {P = P} σ

  Y : subst P refl u ≡ w
  Y = Σ≡-snd {P = P} (cong pair (ψ ∙ ψ'))

  Z : v ≡ w
  Z = sym (substRefl P v) ∙ q'

  step1 : _⊙_ {P = P} {p = refl} q {p' = refl} q' ≡ sym cgS₀ ∙ X
  step1 = substInPathL cgS₀ X

  step2 : X ≡ sym cgW₁ ∙ Y
  step2 = sym (fromPathP (cong (Σ≡-snd {P = P}) T))
          ∙ substInPathL cgW₁ Y

  step345 : Y ≡ q ∙ Z
  step345 =
    fromPathPConst (ψ ∙ ψ')
    ∙ cong (λ r → transportRefl u ∙ (r ∙ ψ')) (toPathPConst q)
    ∙ cong (λ r → transportRefl u ∙ ((sym (transportRefl u) ∙ q) ∙ r))
           (toPathPConst q')
    ∙ sym (∙-assoc (transportRefl u) (sym (transportRefl u) ∙ q) Z)
    ∙ cong (_∙ Z)
           (sym (∙-assoc (transportRefl u) (sym (transportRefl u)) q)
            ∙ cong (_∙ q) (rCancel (transportRefl u))
            ∙ sym (lUnit q))

  end : sym cgS₀ ∙ (sym cgW₁ ∙ (q ∙ Z))
        ≡ cong (λ e → subst P e u) (sym (⊙-reflSquare {P = P} q q'))
          ∙ q ∙ sym (substRefl P v) ∙ q'
  end = sym (∙-assoc (sym cgS₀) (sym cgW₁) (q ∙ Z))
        ∙ cong (_∙ (q ∙ Z)) (sym (symDistr cgW₁ cgS₀))
        ∙ cong (λ r → sym r ∙ (q ∙ Z)) (sym (cong-∙ h W₁ S₀))

------------------------------------------------------------------------
-- Congruence and decomposition laws for Σ≡dep
-- (eq_existT_curried_dep_eq, sigT_map_eq_existT_curried_dep_curried)
------------------------------------------------------------------------

private variable
  ℓp ℓq ℓr ℓs : Level

-- eq_existT_curried_dep_eq: Σ≡dep is a congruence in (H, Hu, Hv).
Σ≡dep-cong : {A : Set ℓ} {P : A → Set ℓ'} {Q : Σ A P → Set ℓ''}
             {x y : A} {H H' : x ≡ y}
             {u : P x} {v : Q (x , u)} {u' : P y} {v' : Q (y , u')}
             {Hu : subst P H u ≡ u'} {Hu' : subst P H' u ≡ u'}
             {Hv : subst Q (Σ≡ {P = P} H Hu) v ≡ v'}
             {Hv' : subst Q (Σ≡ {P = P} H' Hu') v ≡ v'}
             (HH : H ≡ H')
             (HHu : subst (λ H → subst P H u ≡ u') HH Hu ≡ Hu')
             (HHv : subst (λ p → subst Q p v ≡ v')
                          (Σ≡-cong2 {P = P} HH HHu) Hv ≡ Hv')
             → subst (λ H → subst (λ x → Σ (P x) (λ a → Q (x , a))) H (u , v)
                            ≡ (u' , v'))
                     HH
                     (Σ≡dep {P = P} {Q = Q} H Hu Hv)
               ≡ Σ≡dep {P = P} {Q = Q} H' Hu' Hv'
Σ≡dep-cong {P = P} {Q = Q} {H = H} {u = u} {v = v} {u' = u'} {v' = v'}
           {Hu = Hu} HH HHu HHv =
  fromPathP (λ k → Σ≡dep {P = P} {Q = Q}
                         (HH k)
                         (toPathP {P = λ k → subst P (HH k) u ≡ u'} HHu k)
                         (toPathP {P = λ k → subst Q (Σ≡-cong2 {P = P} HH HHu k) v
                                              ≡ v'} HHv k))

-- sigT_map_eq_existT_curried_dep_curried: mapping a fiberwise pair of
-- functions over a dependent Σ-path.
sigT-map-Σ≡dep :
  {A : Set ℓ} {B : Set ℓ'}
  {P : A → Set ℓ''} {R : (a : A) → P a → Set ℓ'''}
  {P' : B → Set ℓp} {R' : (b : B) → P' b → Set ℓr}
  (f : A → B) (g : (a : A) → P a → P' (f a))
  (h : (a : A) (u : P a) → R a u → R' (f a) (g a u))
  {x y : A} {u : P x} {v : R x u} {u' : P y} {v' : R y u'}
  (H : x ≡ y) (Hu : subst P H u ≡ u')
  (Hv : subst (λ z → R (fst z) (snd z)) (Σ≡ {P = P} H Hu) v ≡ v')
  → sigT-map-eq {P = λ a → Σ (P a) (R a)} {Q = λ b → Σ (P' b) (R' b)} {f = f}
                (λ a uv → (g a (fst uv) , h a (fst uv) (snd uv)))
                {p = H}
                (Σ≡dep {P = P} {Q = λ z → R (fst z) (snd z)} H Hu Hv)
    ≡ Σ≡dep {P = P'} {Q = λ z → R' (fst z) (snd z)}
            (cong f H)
            (sigT-map-eq {P = P} {Q = P'} {f = f} g Hu)
            (subst (λ p → subst (λ z → R' (fst z) (snd z)) p (h x u v)
                          ≡ h y u' v')
                   (cong-Σ≡ f g H Hu)
                   (sigT-map-eq {P = λ z → R (fst z) (snd z)}
                                {Q = λ z → R' (fst z) (snd z)}
                                {f = λ z → (f (fst z) , g (fst z) (snd z))}
                                (λ z → h (fst z) (snd z))
                                {p = Σ≡ {P = P} H Hu}
                                Hv))
sigT-map-Σ≡dep {A = A} {B = B} {P = P} {R = R} {P' = P'} {R' = R'}
               f g h {x} {y} {u} {v} {u'} {v'} H Hu Hv =
  lhs≡center
  ∙ cong (λ (w : PathP (λ i → Σ (P' (f (H i))) (R' (f (H i))))
                       (g x u , h x u v) (g y u' , h y u' v'))
            → fromPathP w)
         pairSq
  where
  hu : PathP (λ i → P (H i)) u u'
  hu = toPathP {P = λ i → P (H i)} Hu

  hv : PathP (λ i → R (H i) (hu i)) v v'
  hv = toPathP {P = λ i → R (H i) (hu i)} Hv

  gline : PathP (λ i → P' (f (H i))) (g x u) (g y u')
  gline = λ i → g (H i) (hu i)

  hline : PathP (λ i → R' (f (H i)) (gline i)) (h x u v) (h y u' v')
  hline = λ i → h (H i) (hu i) (hv i)

  center : PathP (λ i → Σ (P' (f (H i))) (R' (f (H i))))
                 (g x u , h x u v) (g y u' , h y u' v')
  center = λ i → (gline i , hline i)

  lhs≡center :
    sigT-map-eq {P = λ a → Σ (P a) (R a)} {Q = λ b → Σ (P' b) (R' b)} {f = f}
                (λ a uv → (g a (fst uv) , h a (fst uv) (snd uv)))
                {p = H}
                (Σ≡dep {P = P} {Q = λ z → R (fst z) (snd z)} H Hu Hv)
    ≡ fromPathP center
  lhs≡center =
    cong (λ (w : PathP (λ i → Σ (P (H i)) (R (H i))) (u , v) (u' , v'))
            → fromPathP {P = λ i → Σ (P' (f (H i))) (R' (f (H i)))}
                        (λ i → (g (H i) (fst (w i))
                               , h (H i) (fst (w i)) (snd (w i)))))
         (toPathP-fromPathP (λ i → Σ (P (H i)) (R (H i)))
                            (λ i → (hu i , hv i)))

  θ1 : PathP (λ k → PathP (λ i → P' (f (H i))) (g x u) (g y u'))
             gline
             (toPathP {P = λ i → P' (f (H i))}
                      (sigT-map-eq {P = P} {Q = P'} {f = f} g Hu))
  θ1 = sym (toPathP-fromPathP (λ i → P' (f (H i))) gline)

  mapHv : subst (λ z → R' (fst z) (snd z))
                (cong {B = λ _ → Σ B P'}
                      (λ z → (f (fst z) , g (fst z) (snd z)))
                      (Σ≡ {P = P} H Hu))
                (h x u v)
          ≡ h y u' v'
  mapHv = sigT-map-eq {P = λ z → R (fst z) (snd z)}
                      {Q = λ z → R' (fst z) (snd z)}
                      {f = λ z → (f (fst z) , g (fst z) (snd z))}
                      (λ z → h (fst z) (snd z))
                      {p = Σ≡ {P = P} H Hu}
                      Hv

  hvR : PathP (λ i → R' (f (H i))
                        (toPathP {P = λ i → P' (f (H i))}
                                 (sigT-map-eq {P = P} {Q = P'}
                                              {f = f} g Hu) i))
              (h x u v) (h y u' v')
  hvR = toPathP {P = λ i → R' (f (H i))
                              (toPathP {P = λ i → P' (f (H i))}
                                       (sigT-map-eq {P = P} {Q = P'}
                                                    {f = f} g Hu) i)}
                (subst (λ p → subst (λ z → R' (fst z) (snd z)) p (h x u v)
                              ≡ h y u' v')
                       (cong-Σ≡ f g H Hu)
                       mapHv)

  θ2 : PathP (λ k → PathP (λ i → R' (f (H i)) (θ1 k i))
                          (h x u v) (h y u' v'))
             hline hvR
  θ2 = subst (λ a → PathP (λ k → PathP (λ i → R' (f (H i)) (θ1 k i))
                                       (h x u v) (h y u' v'))
                          a hvR)
             (toPathP-fromPathP (λ i → R' (f (H i)) (gline i)) hline)
             (toPathP-over {Q = λ z → R' (fst z) (snd z)}
                           (cong-Σ≡ f g H Hu)
                           mapHv)

  pairSq : center
           ≡ (λ i → (toPathP {P = λ i → P' (f (H i))}
                             (sigT-map-eq {P = P} {Q = P'} {f = f} g Hu) i
                     , hvR i))
  pairSq = λ k i → (θ1 k i , θ2 k i)

------------------------------------------------------------------------
-- The hexagon for curried Σ-paths (νGpd/Lemmas.v: eq_existT_curried_hex)
------------------------------------------------------------------------

Σ≡hex :
  {A1 : Set ℓ} {A2 : Set ℓ'} {A3 : Set ℓ''} {B : Set ℓ'''}
  {P1 : A1 → Set ℓp} {P2 : A2 → Set ℓq} {P3 : A3 → Set ℓr}
  {Q : B → Set ℓs}
  (f1 : A1 → B) (g1 : (a : A1) → P1 a → Q (f1 a))
  (f2 : A2 → B) (g2 : (a : A2) → P2 a → Q (f2 a))
  (f3 : A3 → B) (g3 : (a : A3) → P3 a → Q (f3 a))
  {x1 y1 : A1} {u1 : P1 x1} {v1 : P1 y1}
  {x2 y2 : A2} {u2 : P2 x2} {v2 : P2 y2}
  {x3 y3 : A3} {u3 : P3 x3} {v3 : P3 y3}
  {K1 : x1 ≡ y1} {W1 : subst P1 K1 u1 ≡ v1}
  {K2 : x2 ≡ y2} {W2 : subst P2 K2 u2 ≡ v2}
  {K3 : x3 ≡ y3} {W3 : subst P3 K3 u3 ≡ v3}
  {H2 : f1 y1 ≡ f3 x3} {U2 : subst Q H2 (g1 y1 v1) ≡ g3 x3 u3}
  {H1' : f1 x1 ≡ f2 x2} {U1' : subst Q H1' (g1 x1 u1) ≡ g2 x2 u2}
  {H3' : f2 y2 ≡ f3 y3} {U3' : subst Q H3' (g2 y2 v2) ≡ g3 y3 v3}
  (HH : cong f1 K1 ∙ (H2 ∙ cong f3 K3) ≡ H1' ∙ (cong f2 K2 ∙ H3'))
  (HHu : subst (λ h → subst Q h (g1 x1 u1) ≡ g3 y3 v3) HH
               (_⊙_ {P = Q} (sigT-map-eq {P = P1} {Q = Q} {f = f1} g1 W1)
                    (_⊙_ {P = Q} U2
                         (sigT-map-eq {P = P3} {Q = Q} {f = f3} g3 W3)))
         ≡ _⊙_ {P = Q} U1'
               (_⊙_ {P = Q} (sigT-map-eq {P = P2} {Q = Q} {f = f2} g2 W2)
                    U3'))
  → cong {B = λ _ → Σ B Q} (λ z → (f1 (fst z) , g1 (fst z) (snd z)))
         (Σ≡ {P = P1} K1 W1)
    ∙ (Σ≡ {P = Q} H2 U2
       ∙ cong {B = λ _ → Σ B Q} (λ z → (f3 (fst z) , g3 (fst z) (snd z)))
              (Σ≡ {P = P3} K3 W3))
    ≡ Σ≡ {P = Q} H1' U1'
      ∙ (cong {B = λ _ → Σ B Q} (λ z → (f2 (fst z) , g2 (fst z) (snd z)))
              (Σ≡ {P = P2} K2 W2)
         ∙ Σ≡ {P = Q} H3' U3')
Σ≡hex {P1 = P1} {P2 = P2} {P3 = P3} {Q = Q} f1 g1 f2 g2 f3 g3
      {K1 = K1} {W1 = W1} {K2 = K2} {W2 = W2} {K3 = K3} {W3 = W3}
      {H2 = H2} {U2 = U2} {H1' = H1'} {U1' = U1'} {H3' = H3'} {U3' = U3'}
      HH HHu =
  (λ k → cong-Σ≡ f1 g1 K1 W1 k
         ∙ (Σ≡ {P = Q} H2 U2 ∙ cong-Σ≡ f3 g3 K3 W3 k))
  ∙ cong (Σ≡ {P = Q} (cong f1 K1)
             (sigT-map-eq {P = P1} {Q = Q} {f = f1} g1 W1) ∙_)
         (∙-Σ≡ H2 U2 (cong f3 K3)
               (sigT-map-eq {P = P3} {Q = Q} {f = f3} g3 W3))
  ∙ ∙-Σ≡ (cong f1 K1) (sigT-map-eq {P = P1} {Q = Q} {f = f1} g1 W1)
         (H2 ∙ cong f3 K3)
         (_⊙_ {P = Q} U2 (sigT-map-eq {P = P3} {Q = Q} {f = f3} g3 W3))
  ∙ Σ≡-cong2 {P = Q} HH HHu
  ∙ sym (∙-Σ≡ H1' U1' (cong f2 K2 ∙ H3')
              (_⊙_ {P = Q} (sigT-map-eq {P = P2} {Q = Q} {f = f2} g2 W2)
                   U3'))
  ∙ sym (cong (Σ≡ {P = Q} H1' U1' ∙_)
              (∙-Σ≡ (cong f2 K2)
                    (sigT-map-eq {P = P2} {Q = Q} {f = f2} g2 W2)
                    H3' U3'))
  ∙ (λ k → Σ≡ {P = Q} H1' U1'
           ∙ (cong-Σ≡ f2 g2 K2 W2 (~ k) ∙ Σ≡ {P = Q} H3' U3'))

------------------------------------------------------------------------
-- Inductive-equality kit (private).
--
-- permutahedral_coherence (and the destruct-heavy proofs below) are, in
-- Rocq, long chains of destructs where every step reduces
-- definitionally.  Path types cannot be pattern-matched in cubical
-- Agda, but the inductive identity type can (with benign
-- UnsupportedIndexedMatch warnings), and its transId/congId reduce on
-- reflId exactly like Rocq's eq_trans/f_equal.  So: convert the path
-- hypotheses to Id, replay Rocq's destruct chain as reflId matches, and
-- convert back.  All conversions are the pathToId/idToPath round trip
-- plus commutation with ∙ and cong.
------------------------------------------------------------------------

private
  data Id {A : Set ℓ} (x : A) : A → Set ℓ where
    reflId : Id x x

  transId : {x y z : A} → Id x y → Id y z → Id x z
  transId p reflId = p

  congId : (f : A → B) {x y : A} → Id x y → Id (f x) (f y)
  congId f reflId = reflId

  pathToId : {x y : A} → x ≡ y → Id x y
  pathToId {x = x} p = subst (Id x) p reflId

  idToPath : {x y : A} → Id x y → x ≡ y
  idToPath reflId = refl

  pathToId-refl : {x : A} → pathToId (refl {x = x}) ≡ reflId
  pathToId-refl = transportRefl reflId

  idToPath-pathToId : {x y : A} (p : x ≡ y) → idToPath (pathToId p) ≡ p
  idToPath-pathToId p =
    J (λ _ p → idToPath (pathToId p) ≡ p) (cong idToPath pathToId-refl) p

  pathToId-∙ : {x y z : A} (p : x ≡ y) (q : y ≡ z)
               → pathToId (p ∙ q) ≡ transId (pathToId p) (pathToId q)
  pathToId-∙ p q =
    J (λ _ q → pathToId (p ∙ q) ≡ transId (pathToId p) (pathToId q))
      (cong pathToId (sym (rUnit p))
       ∙ sym (cong (transId (pathToId p)) pathToId-refl))
      q

  pathToId-cong : (f : A → B) {x y : A} (p : x ≡ y)
                  → pathToId (cong f p) ≡ congId f (pathToId p)
  pathToId-cong f p =
    J (λ _ p → pathToId (cong f p) ≡ congId f (pathToId p))
      (pathToId-refl ∙ sym (cong (congId f) pathToId-refl))
      p

  -- The three-factor composite p ∙ (q ∙ r), commuted into Id.
  tri : {X : Set ℓ} {a1 a2 a3 a4 : X}
        (p : a1 ≡ a2) (q : a2 ≡ a3) (r : a3 ≡ a4)
        → pathToId (p ∙ (q ∙ r))
          ≡ transId (pathToId p) (transId (pathToId q) (pathToId r))
  tri p q r = pathToId-∙ p (q ∙ r) ∙ cong (transId (pathToId p)) (pathToId-∙ q r)

  -- Convert a hexagon between three-factor composites to Id, rewriting
  -- each factor's Id-image by a supplied identification.
  hexToId : {X : Set ℓ} {a1 a2 a3 a4 a5 a6 : X}
            (p : a1 ≡ a2) (q : a2 ≡ a3) (r : a3 ≡ a4)
            (s : a1 ≡ a5) (t : a5 ≡ a6) (w : a6 ≡ a4)
            {P : Id a1 a2} {Q : Id a2 a3} {R : Id a3 a4}
            {S : Id a1 a5} {T : Id a5 a6} {W : Id a6 a4}
            (cp : pathToId p ≡ P) (cq : pathToId q ≡ Q) (cr : pathToId r ≡ R)
            (cs : pathToId s ≡ S) (ct : pathToId t ≡ T) (cw : pathToId w ≡ W)
            (SQ : p ∙ (q ∙ r) ≡ s ∙ (t ∙ w))
            → Id (transId P (transId Q R)) (transId S (transId T W))
  hexToId p q r s t w cp cq cr cs ct cw SQ =
    pathToId
      ( sym (tri p q r ∙ (λ k → transId (cp k) (transId (cq k) (cr k))))
        ∙ cong pathToId SQ
        ∙ (tri s t w ∙ (λ k → transId (cs k) (transId (ct k) (cw k)))) )

  hexFromId : {X : Set ℓ} {a1 a2 a3 a4 a5 a6 : X}
              (p : a1 ≡ a2) (q : a2 ≡ a3) (r : a3 ≡ a4)
              (s : a1 ≡ a5) (t : a5 ≡ a6) (w : a6 ≡ a4)
              {P : Id a1 a2} {Q : Id a2 a3} {R : Id a3 a4}
              {S : Id a1 a5} {T : Id a5 a6} {W : Id a6 a4}
              (cp : pathToId p ≡ P) (cq : pathToId q ≡ Q) (cr : pathToId r ≡ R)
              (cs : pathToId s ≡ S) (ct : pathToId t ≡ T) (cw : pathToId w ≡ W)
              (SQᴵ : Id (transId P (transId Q R)) (transId S (transId T W)))
              → p ∙ (q ∙ r) ≡ s ∙ (t ∙ w)
  hexFromId p q r s t w cp cq cr cs ct cw SQᴵ =
    sym (idToPath-pathToId (p ∙ (q ∙ r)))
    ∙ cong idToPath
        ( (tri p q r ∙ (λ k → transId (cp k) (transId (cq k) (cr k))))
          ∙ idToPath SQᴵ
          ∙ sym (tri s t w ∙ (λ k → transId (cs k) (transId (ct k) (cw k)))) )
    ∙ idToPath-pathToId (s ∙ (t ∙ w))
