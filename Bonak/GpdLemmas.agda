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
-- Two proof engines are used.  (1) For statements built from Σ≡ (the
-- PathP-pairing λ i → (p i , toPathP q i)): the toPathP/fromPathP
-- round trips, plus an ALGEBRAIC ⊙ (substComposite ∙ cong ∙ q'; fst of
-- an hcomp in Σ only computes up to transp-noise, so the hcomp-based
-- definition was abandoned) and a J-based cong-∙, so every collapsed
-- point is plain transport algebra.  (2) For the destruct-heavy Rocq
-- proofs (permutahedral_coherence, rew_coh2Painting_restr0,
-- rew_coh2Layer): no destruct cascade at all — the goals are flipped
-- into flat form (Sq below) and PASTED, so every step is ordinary path
-- algebra over the naturality lemmas.
--
-- Layout: the Σ-path kit, the permutahedron paste, the two …-Type
-- statements, then their proofs (rew-coh2Painting-restr0 and
-- rew-coh2Layer) with the pasting calculus they run on, and finally the
-- Π-layer bridge (Πcomp suite) that νGpd's mkCoh2Layer consumes.
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

-- J computes on refl, propositionally.
JRefl : {x : A} (P : (y : A) → x ≡ y → Set ℓ') (d : P x refl)
        → J P d refl ≡ d
JRefl P d = transportRefl d

-- cong distributes over ∙ — defined by J (not by an hcomp cube) so
-- that its value at q = refl is JRefl-extractable in terms of rUnit;
-- the refl-computations of the Σ-path kit below all reduce to that.
cong-∙ : (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z)
         → cong f (p ∙ q) ≡ cong f p ∙ cong f q
cong-∙ f p q =
  J (λ _ q → cong f (p ∙ q) ≡ cong f p ∙ cong f q)
    (cong (cong f) (sym (rUnit p)) ∙ rUnit (cong f p))
    q

-- cong-∙ computes at q = refl (via JRefl).
cong-∙-refl : (f : A → B) {x y : A} (p : x ≡ y)
              → cong-∙ f p refl
                ≡ cong (cong f) (sym (rUnit p)) ∙ rUnit (cong f p)
cong-∙-refl f p =
  JRefl (λ _ q → cong f (p ∙ q) ≡ cong f p ∙ cong f q)
        (cong (cong f) (sym (rUnit p)) ∙ rUnit (cong f p))

-- Transport in a path type (endpoint on the left).
substInPathL : {x x' y : A} (e : x ≡ x') (q : x ≡ y)
               → subst (λ w → w ≡ y) e q ≡ sym e ∙ q
substInPathL e q =
  J (λ _ e → subst (λ w → w ≡ _) e q ≡ sym e ∙ q)
    (transportRefl q ∙ lUnit q)
    e

-- substComposite computes at q = refl (via JRefl).
substComposite-refl : {A : Set ℓ} (P : A → Set ℓ') {x y : A}
  (p : x ≡ y) (u : P x)
  → substComposite P p refl u
    ≡ cong (λ e → subst P e u) (sym (rUnit p))
      ∙ sym (substRefl P (subst P p u))
substComposite-refl P p u =
  JRefl (λ _ q → subst P (p ∙ q) u ≡ subst P q (subst P p u))
        (cong (λ e → subst P e u) (sym (rUnit p))
          ∙ sym (substRefl P (subst P p u)))

-- Naturality of substRefl: mapping a fiber path through subst P refl.
substRefl-natural : {A : Set ℓ} {P : A → Set ℓ'} {x : A} {a b : P x}
  (q : a ≡ b)
  → cong (subst P refl) q ≡ substRefl P a ∙ q ∙ sym (substRefl P b)
substRefl-natural {P = P} {a = a} q =
  J (λ b q → cong (subst P refl) q ≡ substRefl P a ∙ q ∙ sym (substRefl P b))
    (sym (cong (substRefl P a ∙_) (sym (lUnit (sym (substRefl P a))))
          ∙ rCancel (substRefl P a)))
    q

-- Cancel an inverse against the head of a composite.
∙-cancel-l : {x₀ x₁ x₂ : A} (s : x₀ ≡ x₁) (M : x₁ ≡ x₂)
             → sym s ∙ s ∙ M ≡ M
∙-cancel-l {x₂ = x₂} s M =
  J (λ _ s → (M : _ ≡ x₂) → sym s ∙ s ∙ M ≡ M)
    (λ M → sym (lUnit (refl ∙ M)) ∙ sym (lUnit M))
    s M

-- Flip a head inverse to the other side of an equation.
∙-flip-l : {x₀ x₁ x₂ : A} (s : x₀ ≡ x₁) {X : x₀ ≡ x₂} {Y : x₁ ≡ x₂}
           → sym s ∙ X ≡ Y → X ≡ s ∙ Y
∙-flip-l s {X} {Y} E =
  lUnit X ∙ cong (_∙ X) (sym (rCancel s)) ∙ ∙-assoc s (sym s) X
  ∙ cong (s ∙_) E

-- substComposite along the image of a map: re-indexing by cong-∙
-- exchanges the composite family transport for the composite path
-- transport.
substComposite-cong : {A : Set ℓ} {B : Set ℓ'} (f : A → B)
  (Q : B → Set ℓ'') {x y z : A}
  (p : x ≡ y) (p' : y ≡ z) (w : Q (f x))
  → substComposite (λ a → Q (f a)) p p' w
    ≡ cong (λ e → subst Q e w) (cong-∙ f p p')
      ∙ substComposite Q (cong f p) (cong f p') w
substComposite-cong {A = A} {B = B} f Q {x = x} {y = y} p p' w =
  J (λ z p' → substComposite (λ a → Q (f a)) p p' w
              ≡ cong (λ e → subst Q e w) (cong-∙ f p p')
                ∙ substComposite Q (cong f p) (cong f p') w)
    (substComposite-refl (λ a → Q (f a)) p w ∙ sym Rchain)
    p'
  where
  h : f x ≡ f y → Q (f y)
  h e = subst Q e w

  C₁ : subst Q (cong f (p ∙ refl)) w ≡ subst Q (cong f p) w
  C₁ = cong h (cong (cong f) (sym (rUnit p)))

  C₂ : subst Q (cong f p) w ≡ subst Q (cong f p ∙ refl) w
  C₂ = cong h (rUnit (cong f p))

  tQ : subst Q refl (subst Q (cong f p) w) ≡ subst Q (cong f p) w
  tQ = substRefl Q (subst Q (cong f p) w)

  Rchain : cong h (cong-∙ f p refl)
           ∙ substComposite Q (cong f p) (cong f refl) w
           ≡ C₁ ∙ sym tQ
  Rchain =
    cong₂ (λ X Y → cong h X ∙ Y)
          (cong-∙-refl f p)
          (substComposite-refl Q (cong f p) w)
    ∙ cong (_∙ (sym C₂ ∙ sym tQ))
           (cong-∙ h (cong (cong f) (sym (rUnit p))) (rUnit (cong f p)))
    ∙ ∙-assoc C₁ C₂ (sym C₂ ∙ sym tQ)
    ∙ cong (C₁ ∙_) (∙-cancel-l (sym C₂) (sym tQ))

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

-- Σ≡dep computes at H = refl: it is definitionally fromPathP of the
-- Σ≡-pairing in the fiber, so fromPathPConst applies.
Σ≡dep-refl : {A : Set ℓ} {P : A → Set ℓ'} {Q : Σ A P → Set ℓ''}
  {x : A} {u : P x} {v : Q (x , u)} {u' : P x} {v' : Q (x , u')}
  (Hu : subst P refl u ≡ u')
  (Hv : subst Q (Σ≡ {P = P} refl Hu) v ≡ v')
  → Σ≡dep {P = P} {Q = Q} refl Hu Hv
    ≡ transportRefl (u , v)
      ∙ Σ≡ {P = λ a → Q (x , a)} (toPathP {P = λ _ → P x} Hu) Hv
Σ≡dep-refl {P = P} {Q = Q} {x = x} Hu Hv =
  fromPathPConst
    (Σ≡ {P = λ a → Q (x , a)} (toPathP {P = λ _ → P x} Hu) Hv)

------------------------------------------------------------------------
-- The Σ-path operations: sigT_map_eq and sigT_trans_eq (⊙)
------------------------------------------------------------------------

-- Rocq's projT2_eq: the second projection of a Σ-path, in subst form.
Σ≡-snd : {P : A → Set ℓ'} {u v : Σ A P} (σ : u ≡ v)
         → subst P (cong fst σ) (snd u) ≡ snd v
Σ≡-snd {P = P} σ = fromPathP (λ i → snd (σ i))

-- rew_map: in cubical, subst (λ a → P (f a)) p x and
-- subst P (cong f p) x are definitionally equal, so rew_map is refl;
-- it is kept as a named lemma so statements can mirror Rocq's 1:1.
rew-map : {A : Set ℓ} {B : Set ℓ'} (P : B → Set ℓ'') (f : A → B)
          {x y : A} (p : x ≡ y) (u : P (f x))
          → subst (λ a → P (f a)) p u ≡ subst P (cong f p) u
rew-map P f p u = refl

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
-- paths.  Defined algebraically (fold the two transports into the
-- composite transport, then chain q and q') rather than through the
-- second projection of an hcomp in Σ: fst of an hcomp in Σ only
-- computes up to transp-noise, and the algebraic form keeps every
-- later computation about ⊙ in plain transport algebra.
sigT-trans-eq : {A : Set ℓ} (P : A → Set ℓ') {x y z : A}
                {u : P x} {v : P y} {w : P z}
                {p : x ≡ y} (q : subst P p u ≡ v)
                {p' : y ≡ z} (q' : subst P p' v ≡ w)
                → subst P (p ∙ p') u ≡ w
sigT-trans-eq P {u = u} {w = w} {p = p} q {p' = p'} q' =
  substComposite P p p' u ∙ cong (subst P p') q ∙ q'

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

private
  -- The two toPathP-refls compose to the (rUnit-rebased) refl ⊙ refl:
  -- the fiber-level content of ∙-Σ≡ at its fully collapsed point.
  toPathP-∙-collapse : {A : Set ℓ} {P : A → Set ℓ'} {x : A} (u : P x)
    → toPathP {P = λ _ → P x} (refl {x = subst P refl u})
      ∙ toPathP {P = λ _ → P x} (refl {x = subst P refl (subst P refl u)})
      ≡ toPathP {P = λ _ → P x}
          (subst (λ r → subst P r u ≡ subst P refl (subst P refl u))
                 (sym (rUnit refl))
                 (_⊙_ {P = P} {p = refl} (refl {x = subst P refl u})
                      {p' = refl}
                      (refl {x = subst P refl (subst P refl u)})))
  toPathP-∙-collapse {A = A} {P = P} {x = x} u =
    cong₂ (λ α β → α ∙ β)
          (toPathPConst refl ∙ sym (rUnit (sym (transportRefl u))))
          (toPathPConst refl ∙ sym (rUnit (sym (transportRefl v₀))))
    ∙ sym (toPathPConst Ŵ
           ∙ cong (sym (transportRefl u) ∙_) Ŵ-chain)
    where
    v₀ w₀ : P x
    v₀ = subst P refl u
    w₀ = subst P refl (subst P refl u)

    g : x ≡ x → P x
    g e = subst P e u

    SC : subst P (refl ∙ refl) u ≡ w₀
    SC = substComposite P refl refl u

    CG′ : subst P (refl ∙ refl) u ≡ subst P refl u
    CG′ = cong g (sym (rUnit refl))

    W : subst P (refl ∙ refl) u ≡ w₀
    W = _⊙_ {P = P} {p = refl} (refl {x = v₀})
             {p' = refl} (refl {x = w₀})

    Ŵ : subst P refl u ≡ w₀
    Ŵ = subst (λ r → subst P r u ≡ w₀) (sym (rUnit refl)) W

    W-chain : W ≡ CG′ ∙ sym (substRefl P v₀)
    W-chain =
      cong (SC ∙_) (sym (lUnit refl))
      ∙ sym (rUnit SC)
      ∙ substComposite-refl P refl u

    Ŵ-chain : Ŵ ≡ sym (substRefl P v₀)
    Ŵ-chain =
      substInPathL CG′ W
      ∙ cong (sym CG′ ∙_) W-chain
      ∙ ∙-cancel-l CG′ (sym (substRefl P v₀))

  -- The value of ∙-Σ≡ at the fully collapsed point of its J-cascade.
  ∙-Σ≡-base : {A : Set ℓ} {P : A → Set ℓ'} {x : A} (u : P x)
    → Σ≡ {P = P} refl (refl {x = subst P refl u})
      ∙ Σ≡ {P = P} refl (refl {x = subst P refl (subst P refl u)})
      ≡ Σ≡ {P = P} (refl ∙ refl)
           (_⊙_ {P = P} {p = refl} (refl {x = subst P refl u})
                {p' = refl} (refl {x = subst P refl (subst P refl u)}))
  ∙-Σ≡-base {A = A} {P = P} {x = x} u =
    sym (cong-∙ (x ,_)
          (toPathP {P = λ _ → P x} (refl {x = subst P refl u}))
          (toPathP {P = λ _ → P x}
                   (refl {x = subst P refl (subst P refl u)})))
    ∙ cong (cong (x ,_)) (toPathP-∙-collapse {P = P} u)
    ∙ sym (Σ≡-cong2 {P = P} {p = refl ∙ refl} {p' = refl}
             {q = _⊙_ {P = P} {p = refl} (refl {x = subst P refl u})
                       {p' = refl}
                       (refl {x = subst P refl (subst P refl u)})}
             (sym (rUnit refl)) refl)

  -- Named motives and stages of ∙-Σ≡'s J-cascade, so that its value at
  -- the collapsed point is JRefl-extractable (∙-Σ≡-refl below).
  module ∙ΣM {ℓa ℓb : Level} {A : Set ℓa} {P : A → Set ℓb}
             {x : A} (u : P x) where
    M₁ : (y : A) → x ≡ y → Set (ℓa ⊔ ℓb)
    M₁ y p = {v : P y} (q : subst P p u ≡ v)
             {z : A} (p' : y ≡ z) {w : P z} (q' : subst P p' v ≡ w)
             → Σ≡ {P = P} p q ∙ Σ≡ {P = P} p' q'
               ≡ Σ≡ {P = P} (p ∙ p') (_⊙_ {P = P} q q')

    M₂ : (v : P x) → subst P refl u ≡ v → Set (ℓa ⊔ ℓb)
    M₂ v q = {z : A} (p' : x ≡ z) {w : P z} (q' : subst P p' v ≡ w)
             → Σ≡ {P = P} refl q ∙ Σ≡ {P = P} p' q'
               ≡ Σ≡ {P = P} (refl ∙ p') (_⊙_ {P = P} q q')

    M₃ : (z : A) → x ≡ z → Set (ℓa ⊔ ℓb)
    M₃ z p' = {w : P z} (q' : subst P p' (subst P refl u) ≡ w)
              → Σ≡ {P = P} refl (refl {x = subst P refl u})
                ∙ Σ≡ {P = P} p' q'
                ≡ Σ≡ {P = P} (refl ∙ p')
                     (_⊙_ {P = P} (refl {x = subst P refl u}) q')

    M₄ : (w : P x) → subst P refl (subst P refl u) ≡ w → Set (ℓa ⊔ ℓb)
    M₄ w q' = Σ≡ {P = P} refl (refl {x = subst P refl u})
              ∙ Σ≡ {P = P} refl q'
              ≡ Σ≡ {P = P} (refl ∙ refl)
                   (_⊙_ {P = P} (refl {x = subst P refl u}) q')

    d₄ : M₄ (subst P refl (subst P refl u)) refl
    d₄ = ∙-Σ≡-base u

    d₃ : M₃ x refl
    d₃ q' = J M₄ d₄ q'

    d₂ : M₂ (subst P refl u) refl
    d₂ p' q' = J M₃ d₃ p' q'

    d₁ : M₁ x refl
    d₁ q p' q' = J M₂ d₂ q p' q'

-- eq_trans_eq_existT_curried
∙-Σ≡ : {A : Set ℓ} {P : A → Set ℓ'} {x y z : A}
       {u : P x} {v : P y} {w : P z}
       (p : x ≡ y) (q : subst P p u ≡ v)
       (p' : y ≡ z) (q' : subst P p' v ≡ w)
       → Σ≡ {P = P} p q ∙ Σ≡ {P = P} p' q'
         ≡ Σ≡ {P = P} (p ∙ p') (_⊙_ {P = P} q q')
∙-Σ≡ {A = A} {P = P} {x = x} {u = u} p q p' q' =
  J (∙ΣM.M₁ u) (∙ΣM.d₁ u) p q p' q'

private
  -- ∙-Σ≡ computes at the collapsed point (via four JRefls).
  ∙-Σ≡-refl : {A : Set ℓ} {P : A → Set ℓ'} {x : A} (u : P x)
    → ∙-Σ≡ {P = P} refl (refl {x = subst P refl u})
           refl (refl {x = subst P refl (subst P refl u)})
      ≡ ∙-Σ≡-base u
  ∙-Σ≡-refl {A = A} {P = P} {x = x} u =
    cong (λ f → f {subst P refl u} refl {x} refl
                  {subst P refl (subst P refl u)} refl)
         (JRefl (∙ΣM.M₁ u) (∙ΣM.d₁ u))
    ∙ cong (λ f → f {x} refl {subst P refl (subst P refl u)} refl)
           (JRefl (∙ΣM.M₂ u) (∙ΣM.d₂ u))
    ∙ cong (λ f → f {subst P refl (subst P refl u)} refl)
           (JRefl (∙ΣM.M₃ u) (∙ΣM.d₃ u))
    ∙ JRefl (∙ΣM.M₄ u) (∙ΣM.d₄ u)

------------------------------------------------------------------------
-- Computation of the operations at refl
-- (sigT_map_eq_refl, sigT_trans_eq_refl)
--
-- NB. Rocq's statements (`sigT_map_eq g (p:=eq_refl) q = f_equal (g x) q`
-- and `sigT_trans_eq (p:=eq_refl) q (p':=eq_refl) q' = eq_trans q q'`)
-- type-check only because `rew eq_refl in u` REDUCES in Rocq; in
-- cubical `subst P refl u` does not, so the ports below carry the
-- transport corrections explicitly (substRefl-conjugations and, for ⊙,
-- the rUnit refl re-indexing of the composite base path).
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

sigT-trans-eq-refl : {A : Set ℓ} {P : A → Set ℓ'} {x : A} {u v w : P x}
                     (q : subst P refl u ≡ v) (q' : subst P refl v ≡ w)
                     → _⊙_ {P = P} {p = refl} q {p' = refl} q'
                       ≡ cong (λ e → subst P e u) (sym (rUnit refl))
                         ∙ q ∙ sym (substRefl P v) ∙ q'
sigT-trans-eq-refl {A = A} {P = P} {x = x} {u = u} {v = v} {w = w} q q' =
  cong (λ X → X ∙ cong (subst P refl) q ∙ q') (substComposite-refl P refl u)
  ∙ cong (λ X → (CG ∙ sym t₀) ∙ X ∙ q') (substRefl-natural {P = P} q)
  ∙ ∙-assoc CG (sym t₀) ((t₀ ∙ q ∙ sym tᵥ) ∙ q')
  ∙ cong (CG ∙_)
      ( cong (sym t₀ ∙_) (∙-assoc t₀ (q ∙ sym tᵥ) q')
        ∙ ∙-cancel-l t₀ ((q ∙ sym tᵥ) ∙ q')
        ∙ ∙-assoc q (sym tᵥ) q' )
  where
  CG : subst P (refl ∙ refl) u ≡ subst P refl u
  CG = cong (λ e → subst P e u) (sym (rUnit refl))

  t₀ : subst P refl (subst P refl u) ≡ subst P refl u
  t₀ = substRefl P (subst P refl u)

  tᵥ : subst P refl v ≡ v
  tᵥ = substRefl P v

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
-- sigT_trans_eq_existT_curried_dep: ⊙ of two Σ≡dep's is a Σ≡dep.
-- The J-cascade mirrors Rocq's destruct order (Hv', Hu', H', Hv, Hu,
-- H); the collapsed point is a computation in one fiber, assembled in
-- the private module ⊙D below from Σ≡dep-refl, substComposite-cong,
-- ∙-Σ≡-refl and toPathP-∙-collapse.
------------------------------------------------------------------------

private
  module ⊙D {ℓa ℓb ℓc : Level} {A : Set ℓa} {P : A → Set ℓb}
            {Q : Σ A P → Set ℓc} {x : A} (u : P x) (v : Q (x , u)) where
    Fam : A → Set (ℓb ⊔ ℓc)
    Fam x' = Σ (P x') (λ a → Q (x' , a))

    P' : P x → Set ℓc
    P' a = Q (x , a)

    v₀ᴾ : P x
    v₀ᴾ = subst P refl u

    σ₀ : _≡_ {A = Σ A P} (x , u) (x , v₀ᴾ)
    σ₀ = Σ≡ {P = P} refl (refl {x = v₀ᴾ})

    v₀Q : Q (x , v₀ᴾ)
    v₀Q = subst Q σ₀ v

    w₀ᴾ : P x
    w₀ᴾ = subst P refl v₀ᴾ

    σ₁ : _≡_ {A = Σ A P} (x , v₀ᴾ) (x , w₀ᴾ)
    σ₁ = Σ≡ {P = P} refl (refl {x = w₀ᴾ})

    w₀Q : Q (x , w₀ᴾ)
    w₀Q = subst Q σ₁ v₀Q

    D₁ : subst Fam refl (u , v) ≡ (v₀ᴾ , v₀Q)
    D₁ = Σ≡dep {P = P} {Q = Q} refl (refl {x = v₀ᴾ}) (refl {x = v₀Q})

    D₂ : subst Fam refl (v₀ᴾ , v₀Q) ≡ (w₀ᴾ , w₀Q)
    D₂ = Σ≡dep {P = P} {Q = Q} refl (refl {x = w₀ᴾ}) (refl {x = w₀Q})

    Â₀ : subst P (refl ∙ refl) u ≡ w₀ᴾ
    Â₀ = _⊙_ {P = P} {p = refl} (refl {x = v₀ᴾ})
              {p' = refl} (refl {x = w₀ᴾ})

    ε : σ₀ ∙ σ₁ ≡ Σ≡ {P = P} (refl ∙ refl) Â₀
    ε = ∙-Σ≡ {P = P} refl (refl {x = v₀ᴾ}) refl (refl {x = w₀ᴾ})

    ΘQ : subst Q (σ₀ ∙ σ₁) v ≡ w₀Q
    ΘQ = _⊙_ {P = Q} {p = σ₀} (refl {x = v₀Q}) {p' = σ₁} (refl {x = w₀Q})

    Fq : (x , u) ≡ (x , w₀ᴾ) → Set ℓc
    Fq ω = subst Q ω v ≡ w₀Q

    B̂₀ : subst Q (Σ≡ {P = P} (refl ∙ refl) Â₀) v ≡ w₀Q
    B̂₀ = subst Fq ε ΘQ

    -- Fiber-level ingredients.
    ψ : u ≡ v₀ᴾ
    ψ = toPathP {P = λ _ → P x} refl

    ψ' : v₀ᴾ ≡ w₀ᴾ
    ψ' = toPathP {P = λ _ → P x} refl

    Â' : subst P refl u ≡ w₀ᴾ
    Â' = subst (λ r → subst P r u ≡ w₀ᴾ) (sym (rUnit refl)) Â₀

    scc : Σ≡ {P = P} (refl ∙ refl) Â₀ ≡ Σ≡ {P = P} refl Â'
    scc = Σ≡-cong2 {P = P} {p = refl ∙ refl} {p' = refl}
                   {q = Â₀} {q' = Â'} (sym (rUnit refl)) refl

    F₁ : σ₀ ∙ σ₁ ≡ cong (x ,_) (ψ ∙ ψ')
    F₁ = sym (cong-∙ (x ,_) ψ ψ')

    Hp : ψ ∙ ψ' ≡ toPathP {P = λ _ → P x} Â'
    Hp = toPathP-∙-collapse {P = P} u

    F₂ : cong (x ,_) (ψ ∙ ψ') ≡ Σ≡ {P = P} refl Â'
    F₂ = cong (cong (x ,_)) Hp

    hQ : (x , u) ≡ (x , w₀ᴾ) → Q (x , w₀ᴾ)
    hQ ω = subst Q ω v

    hP' : u ≡ w₀ᴾ → Q (x , w₀ᴾ)
    hP' r = subst P' r v

    cQ : subst Q (cong (x ,_) (ψ ∙ ψ')) v ≡ subst Q (σ₀ ∙ σ₁) v
    cQ = cong hQ (cong-∙ (x ,_) ψ ψ')

    SCQ : subst Q (σ₀ ∙ σ₁) v ≡ subst Q σ₁ (subst Q σ₀ v)
    SCQ = substComposite Q σ₀ σ₁ v

    Ω : subst P' (ψ ∙ ψ') v ≡ w₀Q
    Ω = _⊙_ {P = P'} {p = ψ} (refl {x = v₀Q}) {p' = ψ'} (refl {x = w₀Q})

    B̂' : subst Q (Σ≡ {P = P} refl Â') v ≡ w₀Q
    B̂' = subst (λ p → subst Q p v ≡ w₀Q) scc B̂₀

    S₁ : _≡_ {A = Fam x} (u , v) (v₀ᴾ , v₀Q)
    S₁ = Σ≡ {P = P'} ψ (refl {x = v₀Q})

    S₂ : _≡_ {A = Fam x} (v₀ᴾ , v₀Q) (w₀ᴾ , w₀Q)
    S₂ = Σ≡ {P = P'} ψ' (refl {x = w₀Q})

    CG-F : subst Fam (refl ∙ refl) (u , v) ≡ subst Fam refl (u , v)
    CG-F = cong (λ e → subst Fam e (u , v)) (sym (rUnit refl))

    SC-F : subst Fam (refl ∙ refl) (u , v)
           ≡ subst Fam refl (subst Fam refl (u , v))
    SC-F = substComposite Fam refl refl (u , v)

    tRa : subst Fam refl (subst Fam refl (u , v)) ≡ subst Fam refl (u , v)
    tRa = substRefl Fam (subst Fam refl (u , v))

    tRb : subst Fam refl (v₀ᴾ , v₀Q) ≡ (v₀ᴾ , v₀Q)
    tRb = transportRefl (v₀ᴾ , v₀Q)

    tRuv : subst Fam refl (u , v) ≡ (u , v)
    tRuv = transportRefl (u , v)

    -- FIN: the fiber-level comparison of the two rebased composites.
    fin7 : Ω ≡ cQ ∙ ΘQ
    fin7 =
      cong (_∙ (refl ∙ refl)) (substComposite-cong (x ,_) Q ψ ψ' v)
      ∙ ∙-assoc cQ SCQ (refl ∙ refl)

    fin3 : ε ∙ scc ≡ F₁ ∙ F₂
    fin3 =
      cong (_∙ scc) (∙-Σ≡-refl u)
      ∙ ∙-assoc F₁ (F₂ ∙ sym scc) scc
      ∙ cong (F₁ ∙_) (∙-assoc F₂ (sym scc) scc)
      ∙ cong (λ Z → F₁ ∙ (F₂ ∙ Z)) (lCancel scc)
      ∙ cong (F₁ ∙_) (sym (rUnit F₂))

    fb : B̂' ≡ subst Fq (F₁ ∙ F₂) ΘQ
    fb = sym (substComposite Fq ε scc ΘQ)
         ∙ cong (λ e → subst Fq e ΘQ) fin3

    bc : subst Fq (F₁ ∙ F₂) ΘQ ≡ sym (cong hP' Hp) ∙ (cQ ∙ ΘQ)
    bc = substInPathL (cong hQ (F₁ ∙ F₂)) ΘQ
         ∙ cong (λ Z → sym Z ∙ ΘQ) (cong-∙ hQ F₁ F₂)
         ∙ cong (_∙ ΘQ) (symDistr (cong hQ F₁) (cong hQ F₂))
         ∙ ∙-assoc (sym (cong hQ F₂)) (sym (cong hQ F₁)) ΘQ

    FIN : subst (λ r → subst P' r v ≡ w₀Q) Hp Ω ≡ B̂'
    FIN = substInPathL (cong hP' Hp) Ω
          ∙ cong (sym (cong hP' Hp) ∙_) fin7
          ∙ sym bc
          ∙ sym fb

    -- The left-hand chain: ⊙ of the two Σ≡dep's, normalized.
    Lc : _⊙_ {P = Fam} {p = refl} D₁ {p' = refl} D₂
         ≡ CG-F ∙ (tRuv ∙ Σ≡ {P = P'} (ψ ∙ ψ') Ω)
    Lc =
      cong (λ X → SC-F ∙ (X ∙ D₂)) (substRefl-natural {P = Fam} D₁)
      ∙ cong (λ X → SC-F ∙ ((tRa ∙ (D₁ ∙ sym tRb)) ∙ X))
             (Σ≡dep-refl {P = P} {Q = Q} (refl {x = w₀ᴾ}) (refl {x = w₀Q}))
      ∙ cong (SC-F ∙_) (∙-assoc tRa (D₁ ∙ sym tRb) (tRb ∙ S₂))
      ∙ cong (λ X → SC-F ∙ (tRa ∙ X)) (∙-assoc D₁ (sym tRb) (tRb ∙ S₂))
      ∙ cong (λ X → SC-F ∙ (tRa ∙ (D₁ ∙ X))) (∙-cancel-l tRb S₂)
      ∙ cong (_∙ (tRa ∙ (D₁ ∙ S₂))) (substComposite-refl Fam refl (u , v))
      ∙ ∙-assoc CG-F (sym tRa) (tRa ∙ (D₁ ∙ S₂))
      ∙ cong (CG-F ∙_) (∙-cancel-l tRa (D₁ ∙ S₂))
      ∙ cong (λ X → CG-F ∙ (X ∙ S₂))
             (Σ≡dep-refl {P = P} {Q = Q} (refl {x = v₀ᴾ}) (refl {x = v₀Q}))
      ∙ cong (CG-F ∙_) (∙-assoc tRuv S₁ S₂)
      ∙ cong (λ X → CG-F ∙ (tRuv ∙ X))
             (∙-Σ≡ {P = P'} {u = v} ψ (refl {x = v₀Q}) ψ' (refl {x = w₀Q}))

    -- The right-hand chain: the composite Σ≡dep, rebased to refl.
    Rc : Σ≡dep {P = P} {Q = Q} (refl ∙ refl) Â₀ B̂₀
         ≡ CG-F ∙ (tRuv ∙ Σ≡ {P = P'} (toPathP {P = λ _ → P x} Â') B̂')
    Rc =
      ∙-flip-l CG-F
        (sym (substInPathL CG-F (Σ≡dep {P = P} {Q = Q} (refl ∙ refl) Â₀ B̂₀))
         ∙ Σ≡dep-cong {P = P} {Q = Q}
             {H = refl ∙ refl} {H' = refl}
             {Hu = Â₀} {Hu' = Â'} {Hv = B̂₀} {Hv' = B̂'}
             (sym (rUnit refl)) refl refl)
      ∙ cong (CG-F ∙_) (Σ≡dep-refl {P = P} {Q = Q} Â' B̂')

    base : _⊙_ {P = Fam} {p = refl} D₁ {p' = refl} D₂
           ≡ Σ≡dep {P = P} {Q = Q} (refl ∙ refl) Â₀ B̂₀
    base =
      Lc
      ∙ cong (λ Z → CG-F ∙ (tRuv ∙ Z))
             (Σ≡-cong2 {P = P'} {p = ψ ∙ ψ'}
                       {p' = toPathP {P = λ _ → P x} Â'}
                       {q = Ω} {q' = B̂'} Hp FIN)
      ∙ sym Rc

    -- The J-cascade, innermost stage first.
    M₆ : (v'' : Q (x , w₀ᴾ)) → subst Q σ₁ v₀Q ≡ v'' → Set (ℓb ⊔ ℓc)
    M₆ v'' Hv' =
      _⊙_ {P = Fam} {p = refl} D₁ {p' = refl}
          (Σ≡dep {P = P} {Q = Q} refl (refl {x = w₀ᴾ}) Hv')
      ≡ Σ≡dep {P = P} {Q = Q} (refl ∙ refl) Â₀
              (subst (λ ω → subst Q ω v ≡ v'') ε
                     (_⊙_ {P = Q} {p = σ₀} (refl {x = v₀Q}) {p' = σ₁} Hv'))

    M₅ : (u'' : P x) → subst P refl v₀ᴾ ≡ u'' → Set (ℓb ⊔ ℓc)
    M₅ u'' Hu' =
      {v'' : Q (x , u'')}
      (Hv' : subst Q (Σ≡ {P = P} refl Hu') v₀Q ≡ v'')
      → _⊙_ {P = Fam} {p = refl} D₁ {p' = refl}
            (Σ≡dep {P = P} {Q = Q} refl Hu' Hv')
        ≡ Σ≡dep {P = P} {Q = Q} (refl ∙ refl)
                (_⊙_ {P = P} {p = refl} (refl {x = v₀ᴾ}) {p' = refl} Hu')
                (subst (λ ω → subst Q ω v ≡ v'')
                       (∙-Σ≡ {P = P} refl (refl {x = v₀ᴾ}) refl Hu')
                       (_⊙_ {P = Q} {p = σ₀} (refl {x = v₀Q})
                            {p' = Σ≡ {P = P} refl Hu'} Hv'))

    M₄ : (z : A) → x ≡ z → Set (ℓb ⊔ ℓc)
    M₄ z H' =
      {u'' : P z} (Hu' : subst P H' v₀ᴾ ≡ u'')
      {v'' : Q (z , u'')}
      (Hv' : subst Q (Σ≡ {P = P} H' Hu') v₀Q ≡ v'')
      → _⊙_ {P = Fam} {p = refl} D₁ {p' = H'}
            (Σ≡dep {P = P} {Q = Q} H' Hu' Hv')
        ≡ Σ≡dep {P = P} {Q = Q} (refl ∙ H')
                (_⊙_ {P = P} {p = refl} (refl {x = v₀ᴾ}) {p' = H'} Hu')
                (subst (λ ω → subst Q ω v ≡ v'')
                       (∙-Σ≡ {P = P} refl (refl {x = v₀ᴾ}) H' Hu')
                       (_⊙_ {P = Q} {p = σ₀} (refl {x = v₀Q})
                            {p' = Σ≡ {P = P} H' Hu'} Hv'))

    M₃ : (v' : Q (x , v₀ᴾ)) → subst Q σ₀ v ≡ v' → Set (ℓa ⊔ ℓb ⊔ ℓc)
    M₃ v' Hv =
      {z : A} (H' : x ≡ z) {u'' : P z} (Hu' : subst P H' v₀ᴾ ≡ u'')
      {v'' : Q (z , u'')}
      (Hv' : subst Q (Σ≡ {P = P} H' Hu') v' ≡ v'')
      → _⊙_ {P = Fam} {p = refl}
            (Σ≡dep {P = P} {Q = Q} refl (refl {x = v₀ᴾ}) Hv) {p' = H'}
            (Σ≡dep {P = P} {Q = Q} H' Hu' Hv')
        ≡ Σ≡dep {P = P} {Q = Q} (refl ∙ H')
                (_⊙_ {P = P} {p = refl} (refl {x = v₀ᴾ}) {p' = H'} Hu')
                (subst (λ ω → subst Q ω v ≡ v'')
                       (∙-Σ≡ {P = P} refl (refl {x = v₀ᴾ}) H' Hu')
                       (_⊙_ {P = Q} {p = σ₀} Hv
                            {p' = Σ≡ {P = P} H' Hu'} Hv'))

    M₂ : (u' : P x) → subst P refl u ≡ u' → Set (ℓa ⊔ ℓb ⊔ ℓc)
    M₂ u' Hu =
      {v' : Q (x , u')} (Hv : subst Q (Σ≡ {P = P} refl Hu) v ≡ v')
      {z : A} (H' : x ≡ z) {u'' : P z} (Hu' : subst P H' u' ≡ u'')
      {v'' : Q (z , u'')}
      (Hv' : subst Q (Σ≡ {P = P} H' Hu') v' ≡ v'')
      → _⊙_ {P = Fam} {p = refl}
            (Σ≡dep {P = P} {Q = Q} refl Hu Hv) {p' = H'}
            (Σ≡dep {P = P} {Q = Q} H' Hu' Hv')
        ≡ Σ≡dep {P = P} {Q = Q} (refl ∙ H')
                (_⊙_ {P = P} {p = refl} Hu {p' = H'} Hu')
                (subst (λ ω → subst Q ω v ≡ v'')
                       (∙-Σ≡ {P = P} refl Hu H' Hu')
                       (_⊙_ {P = Q} {p = Σ≡ {P = P} refl Hu} Hv
                            {p' = Σ≡ {P = P} H' Hu'} Hv'))

    M₁ : (y : A) → x ≡ y → Set (ℓa ⊔ ℓb ⊔ ℓc)
    M₁ y H =
      {u' : P y} (Hu : subst P H u ≡ u')
      {v' : Q (y , u')} (Hv : subst Q (Σ≡ {P = P} H Hu) v ≡ v')
      {z : A} (H' : y ≡ z) {u'' : P z} (Hu' : subst P H' u' ≡ u'')
      {v'' : Q (z , u'')}
      (Hv' : subst Q (Σ≡ {P = P} H' Hu') v' ≡ v'')
      → _⊙_ {P = Fam} {p = H}
            (Σ≡dep {P = P} {Q = Q} H Hu Hv) {p' = H'}
            (Σ≡dep {P = P} {Q = Q} H' Hu' Hv')
        ≡ Σ≡dep {P = P} {Q = Q} (H ∙ H')
                (_⊙_ {P = P} {p = H} Hu {p' = H'} Hu')
                (subst (λ ω → subst Q ω v ≡ v'')
                       (∙-Σ≡ {P = P} H Hu H' Hu')
                       (_⊙_ {P = Q} {p = Σ≡ {P = P} H Hu} Hv
                            {p' = Σ≡ {P = P} H' Hu'} Hv'))

    d₆ : M₆ w₀Q refl
    d₆ = base

    d₅ : M₅ w₀ᴾ refl
    d₅ Hv' = J M₆ d₆ Hv'

    d₄ : M₄ x refl
    d₄ Hu' Hv' = J M₅ d₅ Hu' Hv'

    d₃ : M₃ v₀Q refl
    d₃ H' Hu' Hv' = J M₄ d₄ H' Hu' Hv'

    d₂ : M₂ v₀ᴾ refl
    d₂ Hv H' Hu' Hv' = J M₃ d₃ Hv H' Hu' Hv'

    d₁ : M₁ x refl
    d₁ Hu Hv H' Hu' Hv' = J M₂ d₂ Hu Hv H' Hu' Hv'

⊙-Σ≡dep : {A : Set ℓ} {P : A → Set ℓ'} {Q : Σ A P → Set ℓ''}
  {x y z : A} {u : P x} {v : Q (x , u)} {u' : P y} {v' : Q (y , u')}
  {u'' : P z} {v'' : Q (z , u'')}
  (H : x ≡ y) (Hu : subst P H u ≡ u')
  (Hv : subst Q (Σ≡ {P = P} H Hu) v ≡ v')
  (H' : y ≡ z) (Hu' : subst P H' u' ≡ u'')
  (Hv' : subst Q (Σ≡ {P = P} H' Hu') v' ≡ v'')
  → _⊙_ {P = λ x' → Σ (P x') (λ a → Q (x' , a))} {p = H}
        (Σ≡dep {P = P} {Q = Q} H Hu Hv) {p' = H'}
        (Σ≡dep {P = P} {Q = Q} H' Hu' Hv')
    ≡ Σ≡dep {P = P} {Q = Q} (H ∙ H') (_⊙_ {P = P} {p = H} Hu {p' = H'} Hu')
            (subst (λ ω → subst Q ω v ≡ v'') (∙-Σ≡ {P = P} H Hu H' Hu')
                   (_⊙_ {P = Q} {p = Σ≡ {P = P} H Hu} Hv
                        {p' = Σ≡ {P = P} H' Hu'} Hv'))
⊙-Σ≡dep {P = P} {Q = Q} {u = u} {v = v} H Hu Hv H' Hu' Hv' =
  J (⊙D.M₁ {P = P} {Q = Q} u v) (⊙D.d₁ u v) H Hu Hv H' Hu' Hv'

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
-- eq_existT_curried_dep_hex: the dependent hexagon.  The proof mirrors
-- Rocq's: rewrite three sigT-map-Σ≡dep's and four ⊙-Σ≡dep's, apply
-- Σ≡dep-cong, and close the remaining fiber goal with the abstract
-- tail below (HexT), which replays Rocq's generalize/destruct dance:
-- the seven generalized (Σ≡-composite, lemma-value) singleton pairs
-- are eliminated by J, after which the Σ≡hex transport cell collapses
-- definitionally to refl ∙ … ∙ e6 ∙ … ∙ refl.
------------------------------------------------------------------------

private
  module HexT {ℓs ℓr : Level} {S : Set ℓs} (R : S → Set ℓr)
              {a₀ a₁ a₂ a₃ a₁' a₂' : S}
              (r₀ : R a₀) (r₁ : R a₁) (r₂ : R a₂) (r₃ : R a₃)
              (r₁' : R a₁') (r₂' : R a₂')
              (c₁ : a₀ ≡ a₁) (m₂ : a₁ ≡ a₂) (c₃ : a₂ ≡ a₃)
              (m₁' : a₀ ≡ a₁') (c₂' : a₁' ≡ a₂') (m₃' : a₂' ≡ a₃)
              (w₁ : subst R c₁ r₀ ≡ r₁) (w₂ : subst R m₂ r₁ ≡ r₂)
              (w₃ : subst R c₃ r₂ ≡ r₃)
              (w₁' : subst R m₁' r₀ ≡ r₁')
              (w₂' : subst R c₂' r₁' ≡ r₂')
              (w₃' : subst R m₃' r₂' ≡ r₃)
              where
    F03 : a₀ ≡ a₃ → Set ℓr
    F03 p = subst R p r₀ ≡ r₃

    Tail : (q1 : a₀ ≡ a₁) (e : c₁ ≡ q1)
           (q3 : a₂ ≡ a₃) (e0 : c₃ ≡ q3)
           (q2' : a₁' ≡ a₂') (e1 : c₂' ≡ q2')
           (q23 : a₁ ≡ a₃) (eA : m₂ ∙ q3 ≡ q23)
           (q23' : a₁' ≡ a₃) (eD : q2' ∙ m₃' ≡ q23')
           (qL : a₀ ≡ a₃) (eB : q1 ∙ q23 ≡ qL)
           (qR : a₀ ≡ a₃) (eC : m₁' ∙ q23' ≡ qR)
           (e6 : qL ≡ qR) → Set ℓr
    Tail q1 e q3 e0 q2' e1 q23 eA q23' eD qL eB qR eC e6 =
      (hv : subst F03
              ((λ k → e k ∙ (m₂ ∙ e0 k))
               ∙ cong (q1 ∙_) eA
               ∙ eB
               ∙ e6
               ∙ sym eC
               ∙ sym (cong (m₁' ∙_) eD)
               ∙ (λ k → m₁' ∙ (e1 (~ k) ∙ m₃')))
              (_⊙_ {P = R} {p = c₁} w₁ {p' = m₂ ∙ c₃}
                   (_⊙_ {P = R} {p = m₂} w₂ {p' = c₃} w₃))
            ≡ _⊙_ {P = R} {p = m₁'} w₁' {p' = c₂' ∙ m₃'}
                  (_⊙_ {P = R} {p = c₂'} w₂' {p' = m₃'} w₃'))
      → subst F03 e6
          (subst F03 eB
            (_⊙_ {P = R} {p = q1}
                 (subst (λ p → subst R p r₀ ≡ r₁) e w₁)
                 {p' = q23}
                 (subst (λ p → subst R p r₁ ≡ r₃) eA
                        (_⊙_ {P = R} {p = m₂} w₂ {p' = q3}
                             (subst (λ p → subst R p r₂ ≡ r₃) e0 w₃)))))
        ≡ subst F03 eC
            (_⊙_ {P = R} {p = m₁'} w₁' {p' = q23'}
                 (subst (λ p → subst R p r₁' ≡ r₃) eD
                        (_⊙_ {P = R} {p = q2'}
                             (subst (λ p → subst R p r₁' ≡ r₂') e1 w₂')
                             {p' = m₃'} w₃')))

    base : (e6 : c₁ ∙ (m₂ ∙ c₃) ≡ m₁' ∙ (c₂' ∙ m₃'))
           → Tail c₁ refl c₃ refl c₂' refl
                  (m₂ ∙ c₃) refl (c₂' ∙ m₃') refl
                  (c₁ ∙ (m₂ ∙ c₃)) refl (m₁' ∙ (c₂' ∙ m₃')) refl e6
    base e6 hv =
      cong (subst F03 e6)
           (substRefl F03 X̃
            ∙ cong₂ (λ a b → _⊙_ {P = R} {p = c₁} a {p' = m₂ ∙ c₃} b)
                    (substRefl (λ p → subst R p r₀ ≡ r₁) w₁)
                    (substRefl (λ p → subst R p r₁ ≡ r₃)
                               (_⊙_ {P = R} {p = m₂} w₂ {p' = c₃}
                                    (subst (λ p → subst R p r₂ ≡ r₃)
                                           refl w₃))
                     ∙ cong (λ b → _⊙_ {P = R} {p = m₂} w₂ {p' = c₃} b)
                            (substRefl (λ p → subst R p r₂ ≡ r₃) w₃)))
      ∙ cong (λ w → subst F03 w
                      (_⊙_ {P = R} {p = c₁} w₁ {p' = m₂ ∙ c₃}
                           (_⊙_ {P = R} {p = m₂} w₂ {p' = c₃} w₃)))
             (sym E-collapse)
      ∙ hv
      ∙ sym (substRefl F03 Ỹ
             ∙ cong (λ b → _⊙_ {P = R} {p = m₁'} w₁' {p' = c₂' ∙ m₃'} b)
                    (substRefl (λ p → subst R p r₁' ≡ r₃)
                               (_⊙_ {P = R} {p = c₂'}
                                    (subst (λ p → subst R p r₁' ≡ r₂')
                                           refl w₂')
                                    {p' = m₃'} w₃')
                     ∙ cong (λ a → _⊙_ {P = R} {p = c₂'} a {p' = m₃'} w₃')
                            (substRefl (λ p → subst R p r₁' ≡ r₂') w₂')))
      where
      X̃ : F03 (c₁ ∙ (m₂ ∙ c₃))
      X̃ = _⊙_ {P = R} {p = c₁}
              (subst (λ p → subst R p r₀ ≡ r₁) refl w₁)
              {p' = m₂ ∙ c₃}
              (subst (λ p → subst R p r₁ ≡ r₃) refl
                     (_⊙_ {P = R} {p = m₂} w₂ {p' = c₃}
                          (subst (λ p → subst R p r₂ ≡ r₃) refl w₃)))

      Ỹ : F03 (m₁' ∙ (c₂' ∙ m₃'))
      Ỹ = _⊙_ {P = R} {p = m₁'} w₁' {p' = c₂' ∙ m₃'}
              (subst (λ p → subst R p r₁' ≡ r₃) refl
                     (_⊙_ {P = R} {p = c₂'}
                          (subst (λ p → subst R p r₁' ≡ r₂') refl w₂')
                          {p' = m₃'} w₃'))

      E-collapse : refl ∙ (refl ∙ (refl ∙ (e6 ∙ (refl ∙ (refl ∙ refl)))))
                   ≡ e6
      E-collapse =
        sym (lUnit _) ∙ sym (lUnit _) ∙ sym (lUnit _)
        ∙ cong (e6 ∙_) (sym (lUnit (refl ∙ refl)))
        ∙ cong (e6 ∙_) (sym (lUnit refl))
        ∙ sym (rUnit e6)

    tail : (q1 : a₀ ≡ a₁) (e : c₁ ≡ q1)
           (q3 : a₂ ≡ a₃) (e0 : c₃ ≡ q3)
           (q2' : a₁' ≡ a₂') (e1 : c₂' ≡ q2')
           (q23 : a₁ ≡ a₃) (eA : m₂ ∙ q3 ≡ q23)
           (q23' : a₁' ≡ a₃) (eD : q2' ∙ m₃' ≡ q23')
           (qL : a₀ ≡ a₃) (eB : q1 ∙ q23 ≡ qL)
           (qR : a₀ ≡ a₃) (eC : m₁' ∙ q23' ≡ qR)
           (e6 : qL ≡ qR)
           → Tail q1 e q3 e0 q2' e1 q23 eA q23' eD qL eB qR eC e6
    tail q1 e =
      J (λ q1 e →
           (q3 : a₂ ≡ a₃) (e0 : c₃ ≡ q3)
           (q2' : a₁' ≡ a₂') (e1 : c₂' ≡ q2')
           (q23 : a₁ ≡ a₃) (eA : m₂ ∙ q3 ≡ q23)
           (q23' : a₁' ≡ a₃) (eD : q2' ∙ m₃' ≡ q23')
           (qL : a₀ ≡ a₃) (eB : q1 ∙ q23 ≡ qL)
           (qR : a₀ ≡ a₃) (eC : m₁' ∙ q23' ≡ qR)
           (e6 : qL ≡ qR)
           → Tail q1 e q3 e0 q2' e1 q23 eA q23' eD qL eB qR eC e6)
        (λ q3 e0 →
          J (λ q3 e0 →
               (q2' : a₁' ≡ a₂') (e1 : c₂' ≡ q2')
               (q23 : a₁ ≡ a₃) (eA : m₂ ∙ q3 ≡ q23)
               (q23' : a₁' ≡ a₃) (eD : q2' ∙ m₃' ≡ q23')
               (qL : a₀ ≡ a₃) (eB : c₁ ∙ q23 ≡ qL)
               (qR : a₀ ≡ a₃) (eC : m₁' ∙ q23' ≡ qR)
               (e6 : qL ≡ qR)
               → Tail c₁ refl q3 e0 q2' e1 q23 eA q23' eD qL eB qR eC e6)
            (λ q2' e1 →
              J (λ q2' e1 →
                   (q23 : a₁ ≡ a₃) (eA : m₂ ∙ c₃ ≡ q23)
                   (q23' : a₁' ≡ a₃) (eD : q2' ∙ m₃' ≡ q23')
                   (qL : a₀ ≡ a₃) (eB : c₁ ∙ q23 ≡ qL)
                   (qR : a₀ ≡ a₃) (eC : m₁' ∙ q23' ≡ qR)
                   (e6 : qL ≡ qR)
                   → Tail c₁ refl c₃ refl q2' e1 q23 eA q23' eD
                          qL eB qR eC e6)
                (λ q23 eA →
                  J (λ q23 eA →
                       (q23' : a₁' ≡ a₃) (eD : c₂' ∙ m₃' ≡ q23')
                       (qL : a₀ ≡ a₃) (eB : c₁ ∙ q23 ≡ qL)
                       (qR : a₀ ≡ a₃) (eC : m₁' ∙ q23' ≡ qR)
                       (e6 : qL ≡ qR)
                       → Tail c₁ refl c₃ refl c₂' refl q23 eA q23' eD
                              qL eB qR eC e6)
                    (λ q23' eD →
                      J (λ q23' eD →
                           (qL : a₀ ≡ a₃) (eB : c₁ ∙ (m₂ ∙ c₃) ≡ qL)
                           (qR : a₀ ≡ a₃) (eC : m₁' ∙ q23' ≡ qR)
                           (e6 : qL ≡ qR)
                           → Tail c₁ refl c₃ refl c₂' refl
                                  (m₂ ∙ c₃) refl q23' eD qL eB qR eC e6)
                        (λ qL eB →
                          J (λ qL eB →
                               (qR : a₀ ≡ a₃)
                               (eC : m₁' ∙ (c₂' ∙ m₃') ≡ qR)
                               (e6 : qL ≡ qR)
                               → Tail c₁ refl c₃ refl c₂' refl
                                      (m₂ ∙ c₃) refl (c₂' ∙ m₃') refl
                                      qL eB qR eC e6)
                            (λ qR eC →
                              J (λ qR eC →
                                   (e6 : c₁ ∙ (m₂ ∙ c₃) ≡ qR)
                                   → Tail c₁ refl c₃ refl c₂' refl
                                          (m₂ ∙ c₃) refl (c₂' ∙ m₃') refl
                                          (c₁ ∙ (m₂ ∙ c₃)) refl qR eC e6)
                                base
                                eC)
                            eB)
                        eD)
                    eA)
                e1)
            e0)
        e

Σ≡dep-hex :
  {A0 : Set ℓ} {B : Set ℓ'} {P0 : A0 → Set ℓ''}
  {R0 : (a : A0) → P0 a → Set ℓ'''}
  {P' : B → Set ℓp} {R' : (b : B) → P' b → Set ℓq}
  (f1 : A0 → B) (g1 : (a : A0) → P0 a → P' (f1 a))
  (h1 : (a : A0) (u : P0 a) → R0 a u → R' (f1 a) (g1 a u))
  (f3 : A0 → B) (g3 : (a : A0) → P0 a → P' (f3 a))
  (h3 : (a : A0) (u : P0 a) → R0 a u → R' (f3 a) (g3 a u))
  (f2 : A0 → B) (g2 : (a : A0) → P0 a → P' (f2 a))
  (h2 : (a : A0) (u : P0 a) → R0 a u → R' (f2 a) (g2 a u))
  {x0 x1 x2 x3 x1' x2' : A0}
  {u0 : P0 x0} {v0 : R0 x0 u0} {u1 : P0 x1} {v1 : R0 x1 u1}
  {u2 : P0 x2} {v2 : R0 x2 u2} {u3 : P0 x3} {v3 : R0 x3 u3}
  {u1' : P0 x1'} {v1' : R0 x1' u1'} {u2' : P0 x2'} {v2' : R0 x2' u2'}
  (H1 : x0 ≡ x1) (Hu1 : subst P0 H1 u0 ≡ u1)
  (Hv1 : subst (λ z → R0 (fst z) (snd z)) (Σ≡ {P = P0} H1 Hu1) v0 ≡ v1)
  (H2 : f1 x1 ≡ f3 x2) (Hu2 : subst P' H2 (g1 x1 u1) ≡ g3 x2 u2)
  (Hv2 : subst (λ z → R' (fst z) (snd z)) (Σ≡ {P = P'} H2 Hu2)
               (h1 x1 u1 v1) ≡ h3 x2 u2 v2)
  (H3 : x2 ≡ x3) (Hu3 : subst P0 H3 u2 ≡ u3)
  (Hv3 : subst (λ z → R0 (fst z) (snd z)) (Σ≡ {P = P0} H3 Hu3) v2 ≡ v3)
  (H1' : f1 x0 ≡ f2 x1') (Hu1' : subst P' H1' (g1 x0 u0) ≡ g2 x1' u1')
  (Hv1' : subst (λ z → R' (fst z) (snd z)) (Σ≡ {P = P'} H1' Hu1')
                (h1 x0 u0 v0) ≡ h2 x1' u1' v1')
  (H2' : x1' ≡ x2') (Hu2' : subst P0 H2' u1' ≡ u2')
  (Hv2' : subst (λ z → R0 (fst z) (snd z)) (Σ≡ {P = P0} H2' Hu2')
                v1' ≡ v2')
  (H3' : f2 x2' ≡ f3 x3) (Hu3' : subst P' H3' (g2 x2' u2') ≡ g3 x3 u3)
  (Hv3' : subst (λ z → R' (fst z) (snd z)) (Σ≡ {P = P'} H3' Hu3')
                (h2 x2' u2' v2') ≡ h3 x3 u3 v3)
  (HH : cong f1 H1 ∙ (H2 ∙ cong f3 H3) ≡ H1' ∙ (cong f2 H2' ∙ H3'))
  (HHu : subst (λ h → subst P' h (g1 x0 u0) ≡ g3 x3 u3) HH
               (_⊙_ {P = P'} {p = cong f1 H1}
                    (sigT-map-eq {P = P0} {Q = P'} {f = f1} g1 Hu1)
                    {p' = H2 ∙ cong f3 H3}
                    (_⊙_ {P = P'} {p = H2} Hu2 {p' = cong f3 H3}
                         (sigT-map-eq {P = P0} {Q = P'} {f = f3} g3 Hu3)))
         ≡ _⊙_ {P = P'} {p = H1'} Hu1' {p' = cong f2 H2' ∙ H3'}
               (_⊙_ {P = P'} {p = cong f2 H2'}
                    (sigT-map-eq {P = P0} {Q = P'} {f = f2} g2 Hu2')
                    {p' = H3'} Hu3'))
  (HHv : subst (λ p → subst (λ z → R' (fst z) (snd z)) p (h1 x0 u0 v0)
                      ≡ h3 x3 u3 v3)
               (Σ≡hex {P1 = P0} {P2 = P0} {P3 = P0} {Q = P'}
                      f1 g1 f2 g2 f3 g3
                      {K1 = H1} {W1 = Hu1} {K2 = H2'} {W2 = Hu2'}
                      {K3 = H3} {W3 = Hu3} {H2 = H2} {U2 = Hu2}
                      {H1' = H1'} {U1' = Hu1'} {H3' = H3'} {U3' = Hu3'}
                      HH HHu)
               (_⊙_ {P = λ z → R' (fst z) (snd z)}
                    {p = cong {B = λ _ → Σ B P'} (λ z → (f1 (fst z) , g1 (fst z) (snd z)))
                              (Σ≡ {P = P0} H1 Hu1)}
                    (sigT-map-eq {P = λ z → R0 (fst z) (snd z)}
                                 {Q = λ z → R' (fst z) (snd z)}
                                 {f = λ z → (f1 (fst z) , g1 (fst z) (snd z))}
                                 (λ z → h1 (fst z) (snd z))
                                 {p = Σ≡ {P = P0} H1 Hu1} Hv1)
                    {p' = Σ≡ {P = P'} H2 Hu2
                          ∙ cong {B = λ _ → Σ B P'} (λ z → (f3 (fst z) , g3 (fst z) (snd z)))
                                 (Σ≡ {P = P0} H3 Hu3)}
                    (_⊙_ {P = λ z → R' (fst z) (snd z)}
                         {p = Σ≡ {P = P'} H2 Hu2} Hv2
                         {p' = cong {B = λ _ → Σ B P'} (λ z → (f3 (fst z) , g3 (fst z) (snd z)))
                                    (Σ≡ {P = P0} H3 Hu3)}
                         (sigT-map-eq {P = λ z → R0 (fst z) (snd z)}
                                      {Q = λ z → R' (fst z) (snd z)}
                                      {f = λ z → (f3 (fst z) , g3 (fst z) (snd z))}
                                      (λ z → h3 (fst z) (snd z))
                                      {p = Σ≡ {P = P0} H3 Hu3} Hv3)))
         ≡ _⊙_ {P = λ z → R' (fst z) (snd z)}
               {p = Σ≡ {P = P'} H1' Hu1'} Hv1'
               {p' = cong {B = λ _ → Σ B P'} (λ z → (f2 (fst z) , g2 (fst z) (snd z)))
                          (Σ≡ {P = P0} H2' Hu2') ∙ Σ≡ {P = P'} H3' Hu3'}
               (_⊙_ {P = λ z → R' (fst z) (snd z)}
                    {p = cong {B = λ _ → Σ B P'} (λ z → (f2 (fst z) , g2 (fst z) (snd z)))
                              (Σ≡ {P = P0} H2' Hu2')}
                    (sigT-map-eq {P = λ z → R0 (fst z) (snd z)}
                                 {Q = λ z → R' (fst z) (snd z)}
                                 {f = λ z → (f2 (fst z) , g2 (fst z) (snd z))}
                                 (λ z → h2 (fst z) (snd z))
                                 {p = Σ≡ {P = P0} H2' Hu2'} Hv2')
                    {p' = Σ≡ {P = P'} H3' Hu3'} Hv3'))
  → subst (λ h → subst (λ x → Σ (P' x) (λ a → R' x a)) h
                       (g1 x0 u0 , h1 x0 u0 v0)
                 ≡ (g3 x3 u3 , h3 x3 u3 v3)) HH
      (_⊙_ {P = λ x → Σ (P' x) (λ a → R' x a)} {p = cong f1 H1}
           (sigT-map-eq {P = λ a → Σ (P0 a) (R0 a)}
                        {Q = λ b → Σ (P' b) (R' b)} {f = f1}
                        (λ a uv → (g1 a (fst uv) , h1 a (fst uv) (snd uv)))
                        {p = H1}
                        (Σ≡dep {P = P0} {Q = λ z → R0 (fst z) (snd z)}
                               H1 Hu1 Hv1))
           {p' = H2 ∙ cong f3 H3}
           (_⊙_ {P = λ x → Σ (P' x) (λ a → R' x a)} {p = H2}
                (Σ≡dep {P = P'} {Q = λ z → R' (fst z) (snd z)} H2 Hu2 Hv2)
                {p' = cong f3 H3}
                (sigT-map-eq {P = λ a → Σ (P0 a) (R0 a)}
                             {Q = λ b → Σ (P' b) (R' b)} {f = f3}
                             (λ a uv → (g3 a (fst uv) , h3 a (fst uv) (snd uv)))
                             {p = H3}
                             (Σ≡dep {P = P0} {Q = λ z → R0 (fst z) (snd z)}
                                    H3 Hu3 Hv3))))
    ≡ _⊙_ {P = λ x → Σ (P' x) (λ a → R' x a)} {p = H1'}
          (Σ≡dep {P = P'} {Q = λ z → R' (fst z) (snd z)} H1' Hu1' Hv1')
          {p' = cong f2 H2' ∙ H3'}
          (_⊙_ {P = λ x → Σ (P' x) (λ a → R' x a)} {p = cong f2 H2'}
               (sigT-map-eq {P = λ a → Σ (P0 a) (R0 a)}
                            {Q = λ b → Σ (P' b) (R' b)} {f = f2}
                            (λ a uv → (g2 a (fst uv) , h2 a (fst uv) (snd uv)))
                            {p = H2'}
                            (Σ≡dep {P = P0} {Q = λ z → R0 (fst z) (snd z)}
                                   H2' Hu2' Hv2'))
               {p' = H3'}
               (Σ≡dep {P = P'} {Q = λ z → R' (fst z) (snd z)} H3' Hu3' Hv3'))
Σ≡dep-hex {A0 = A0} {B = B} {P0 = P0} {R0 = R0} {P' = P'} {R' = R'}
  f1 g1 h1 f3 g3 h3 f2 g2 h2
  {x0} {x1} {x2} {x3} {x1'} {x2'}
  {u0} {v0} {u1} {v1} {u2} {v2} {u3} {v3} {u1'} {v1'} {u2'} {v2'}
  H1 Hu1 Hv1 H2 Hu2 Hv2 H3 Hu3 Hv3
  H1' Hu1' Hv1' H2' Hu2' Hv2' H3' Hu3' Hv3' HH HHu HHv =
  (λ k → subst FH HH
           (_⊙_ {P = FP'} {p = cong f1 H1}
                (sigT-map-Σ≡dep {P = P0} {R = R0} {P' = P'} {R' = R'}
                                f1 g1 h1 H1 Hu1 Hv1 k)
                {p' = H2 ∙ cong f3 H3}
                (_⊙_ {P = FP'} {p = H2} X₂ {p' = cong f3 H3}
                     (sigT-map-Σ≡dep {P = P0} {R = R0} {P' = P'} {R' = R'}
                                     f3 g3 h3 H3 Hu3 Hv3 k))))
  ∙ (λ k → subst FH HH
             (_⊙_ {P = FP'} {p = cong f1 H1} X₁' {p' = H2 ∙ cong f3 H3}
                  (⊙-Σ≡dep {P = P'} {Q = R'unc} H2 Hu2 Hv2
                           (cong f3 H3) mg3 Ṽ₃ k)))
  ∙ cong (subst FH HH)
         (⊙-Σ≡dep {P = P'} {Q = R'unc} (cong f1 H1) mg1 Ṽ₁
                  (H2 ∙ cong f3 H3) Hu23 B̃)
  ∙ Σ≡dep-cong {P = P'} {Q = R'unc}
      {H = cong f1 H1 ∙ (H2 ∙ cong f3 H3)}
      {H' = H1' ∙ (cong f2 H2' ∙ H3')}
      {Hu = UL} {Hu' = UR} {Hv = VL} {Hv' = VR}
      HH HHu TAILINST
  ∙ sym (⊙-Σ≡dep {P = P'} {Q = R'unc} H1' Hu1' Hv1'
                 (cong f2 H2' ∙ H3') Hu23' B̃')
  ∙ sym (λ k → _⊙_ {P = FP'} {p = H1'} Y₁ {p' = cong f2 H2' ∙ H3'}
                   (⊙-Σ≡dep {P = P'} {Q = R'unc} (cong f2 H2') mg2 Ṽ₂'
                            H3' Hu3' Hv3' k))
  ∙ sym (λ k → _⊙_ {P = FP'} {p = H1'} Y₁ {p' = cong f2 H2' ∙ H3'}
                   (_⊙_ {P = FP'} {p = cong f2 H2'}
                        (sigT-map-Σ≡dep {P = P0} {R = R0} {P' = P'} {R' = R'}
                                        f2 g2 h2 H2' Hu2' Hv2' k)
                        {p' = H3'} Y₃))
  where
  R'unc : Σ B P' → Set _
  R'unc z = R' (fst z) (snd z)

  R0unc : Σ A0 P0 → Set _
  R0unc z = R0 (fst z) (snd z)

  FP' : B → Set _
  FP' x = Σ (P' x) (λ a → R' x a)

  FH : f1 x0 ≡ f3 x3 → Set _
  FH h = subst FP' h (g1 x0 u0 , h1 x0 u0 v0) ≡ (g3 x3 u3 , h3 x3 u3 v3)

  pm1 pm3 pm2 : Σ A0 P0 → Σ B P'
  pm1 z = (f1 (fst z) , g1 (fst z) (snd z))
  pm3 z = (f3 (fst z) , g3 (fst z) (snd z))
  pm2 z = (f2 (fst z) , g2 (fst z) (snd z))

  mg1 : subst P' (cong f1 H1) (g1 x0 u0) ≡ g1 x1 u1
  mg1 = sigT-map-eq {P = P0} {Q = P'} {f = f1} g1 Hu1

  mg3 : subst P' (cong f3 H3) (g3 x2 u2) ≡ g3 x3 u3
  mg3 = sigT-map-eq {P = P0} {Q = P'} {f = f3} g3 Hu3

  mg2 : subst P' (cong f2 H2') (g2 x1' u1') ≡ g2 x2' u2'
  mg2 = sigT-map-eq {P = P0} {Q = P'} {f = f2} g2 Hu2'

  X₂ : subst FP' H2 (g1 x1 u1 , h1 x1 u1 v1) ≡ (g3 x2 u2 , h3 x2 u2 v2)
  X₂ = Σ≡dep {P = P'} {Q = R'unc} H2 Hu2 Hv2

  Y₁ : subst FP' H1' (g1 x0 u0 , h1 x0 u0 v0) ≡ (g2 x1' u1' , h2 x1' u1' v1')
  Y₁ = Σ≡dep {P = P'} {Q = R'unc} H1' Hu1' Hv1'

  Y₃ : subst FP' H3' (g2 x2' u2' , h2 x2' u2' v2') ≡ (g3 x3 u3 , h3 x3 u3 v3)
  Y₃ = Σ≡dep {P = P'} {Q = R'unc} H3' Hu3' Hv3'

  w₁ : subst R'unc (cong pm1 (Σ≡ {P = P0} H1 Hu1)) (h1 x0 u0 v0)
       ≡ h1 x1 u1 v1
  w₁ = sigT-map-eq {P = R0unc} {Q = R'unc} {f = pm1}
                   (λ z → h1 (fst z) (snd z))
                   {p = Σ≡ {P = P0} H1 Hu1} Hv1

  w₃ : subst R'unc (cong pm3 (Σ≡ {P = P0} H3 Hu3)) (h3 x2 u2 v2)
       ≡ h3 x3 u3 v3
  w₃ = sigT-map-eq {P = R0unc} {Q = R'unc} {f = pm3}
                   (λ z → h3 (fst z) (snd z))
                   {p = Σ≡ {P = P0} H3 Hu3} Hv3

  w₂' : subst R'unc (cong pm2 (Σ≡ {P = P0} H2' Hu2')) (h2 x1' u1' v1')
        ≡ h2 x2' u2' v2'
  w₂' = sigT-map-eq {P = R0unc} {Q = R'unc} {f = pm2}
                    (λ z → h2 (fst z) (snd z))
                    {p = Σ≡ {P = P0} H2' Hu2'} Hv2'

  q1v : _≡_ {A = Σ B P'} (f1 x0 , g1 x0 u0) (f1 x1 , g1 x1 u1)
  q1v = Σ≡ {P = P'} (cong f1 H1) mg1

  q3v : _≡_ {A = Σ B P'} (f3 x2 , g3 x2 u2) (f3 x3 , g3 x3 u3)
  q3v = Σ≡ {P = P'} (cong f3 H3) mg3

  q2'v : _≡_ {A = Σ B P'} (f2 x1' , g2 x1' u1') (f2 x2' , g2 x2' u2')
  q2'v = Σ≡ {P = P'} (cong f2 H2') mg2

  Hu23 : subst P' (H2 ∙ cong f3 H3) (g1 x1 u1) ≡ g3 x3 u3
  Hu23 = _⊙_ {P = P'} {p = H2} Hu2 {p' = cong f3 H3} mg3

  Hu23' : subst P' (cong f2 H2' ∙ H3') (g2 x1' u1') ≡ g3 x3 u3
  Hu23' = _⊙_ {P = P'} {p = cong f2 H2'} mg2 {p' = H3'} Hu3'

  UL : subst P' (cong f1 H1 ∙ (H2 ∙ cong f3 H3)) (g1 x0 u0) ≡ g3 x3 u3
  UL = _⊙_ {P = P'} {p = cong f1 H1} mg1 {p' = H2 ∙ cong f3 H3} Hu23

  UR : subst P' (H1' ∙ (cong f2 H2' ∙ H3')) (g1 x0 u0) ≡ g3 x3 u3
  UR = _⊙_ {P = P'} {p = H1'} Hu1' {p' = cong f2 H2' ∙ H3'} Hu23'

  Ṽ₁ : subst R'unc q1v (h1 x0 u0 v0) ≡ h1 x1 u1 v1
  Ṽ₁ = subst (λ p → subst R'unc p (h1 x0 u0 v0) ≡ h1 x1 u1 v1)
             (cong-Σ≡ f1 g1 H1 Hu1) w₁

  Ṽ₃ : subst R'unc q3v (h3 x2 u2 v2) ≡ h3 x3 u3 v3
  Ṽ₃ = subst (λ p → subst R'unc p (h3 x2 u2 v2) ≡ h3 x3 u3 v3)
             (cong-Σ≡ f3 g3 H3 Hu3) w₃

  Ṽ₂' : subst R'unc q2'v (h2 x1' u1' v1') ≡ h2 x2' u2' v2'
  Ṽ₂' = subst (λ p → subst R'unc p (h2 x1' u1' v1') ≡ h2 x2' u2' v2')
              (cong-Σ≡ f2 g2 H2' Hu2') w₂'

  X₁' : subst FP' (cong f1 H1) (g1 x0 u0 , h1 x0 u0 v0)
        ≡ (g1 x1 u1 , h1 x1 u1 v1)
  X₁' = Σ≡dep {P = P'} {Q = R'unc} (cong f1 H1) mg1 Ṽ₁

  B̃ : subst R'unc (Σ≡ {P = P'} (H2 ∙ cong f3 H3) Hu23) (h1 x1 u1 v1)
      ≡ h3 x3 u3 v3
  B̃ = subst (λ ω → subst R'unc ω (h1 x1 u1 v1) ≡ h3 x3 u3 v3)
            (∙-Σ≡ {P = P'} H2 Hu2 (cong f3 H3) mg3)
            (_⊙_ {P = R'unc} {p = Σ≡ {P = P'} H2 Hu2} Hv2
                 {p' = q3v} Ṽ₃)

  B̃' : subst R'unc (Σ≡ {P = P'} (cong f2 H2' ∙ H3') Hu23') (h2 x1' u1' v1')
       ≡ h3 x3 u3 v3
  B̃' = subst (λ ω → subst R'unc ω (h2 x1' u1' v1') ≡ h3 x3 u3 v3)
             (∙-Σ≡ {P = P'} (cong f2 H2') mg2 H3' Hu3')
             (_⊙_ {P = R'unc} {p = q2'v} Ṽ₂'
                  {p' = Σ≡ {P = P'} H3' Hu3'} Hv3')

  VL : subst R'unc (Σ≡ {P = P'} (cong f1 H1 ∙ (H2 ∙ cong f3 H3)) UL)
             (h1 x0 u0 v0)
       ≡ h3 x3 u3 v3
  VL = subst (λ ω → subst R'unc ω (h1 x0 u0 v0) ≡ h3 x3 u3 v3)
             (∙-Σ≡ {P = P'} (cong f1 H1) mg1 (H2 ∙ cong f3 H3) Hu23)
             (_⊙_ {P = R'unc} {p = q1v} Ṽ₁
                  {p' = Σ≡ {P = P'} (H2 ∙ cong f3 H3) Hu23} B̃)

  VR : subst R'unc (Σ≡ {P = P'} (H1' ∙ (cong f2 H2' ∙ H3')) UR)
             (h1 x0 u0 v0)
       ≡ h3 x3 u3 v3
  VR = subst (λ ω → subst R'unc ω (h1 x0 u0 v0) ≡ h3 x3 u3 v3)
             (∙-Σ≡ {P = P'} H1' Hu1' (cong f2 H2' ∙ H3') Hu23')
             (_⊙_ {P = R'unc} {p = Σ≡ {P = P'} H1' Hu1'} Hv1'
                  {p' = Σ≡ {P = P'} (cong f2 H2' ∙ H3') Hu23'} B̃')

  TAILINST : subst (λ p → subst R'unc p (h1 x0 u0 v0) ≡ h3 x3 u3 v3)
                   (Σ≡-cong2 {P = P'}
                             {p = cong f1 H1 ∙ (H2 ∙ cong f3 H3)}
                             {p' = H1' ∙ (cong f2 H2' ∙ H3')}
                             {q = UL} {q' = UR} HH HHu)
                   VL
             ≡ VR
  TAILINST =
    HexT.tail R'unc
      {a₀ = (f1 x0 , g1 x0 u0)} {a₁ = (f1 x1 , g1 x1 u1)}
      {a₂ = (f3 x2 , g3 x2 u2)} {a₃ = (f3 x3 , g3 x3 u3)}
      {a₁' = (f2 x1' , g2 x1' u1')} {a₂' = (f2 x2' , g2 x2' u2')}
      (h1 x0 u0 v0) (h1 x1 u1 v1) (h3 x2 u2 v2) (h3 x3 u3 v3)
      (h2 x1' u1' v1') (h2 x2' u2' v2')
      (cong pm1 (Σ≡ {P = P0} H1 Hu1)) (Σ≡ {P = P'} H2 Hu2)
      (cong pm3 (Σ≡ {P = P0} H3 Hu3))
      (Σ≡ {P = P'} H1' Hu1') (cong pm2 (Σ≡ {P = P0} H2' Hu2'))
      (Σ≡ {P = P'} H3' Hu3')
      w₁ Hv2 w₃ Hv1' w₂' Hv3'
      q1v (cong-Σ≡ f1 g1 H1 Hu1)
      q3v (cong-Σ≡ f3 g3 H3 Hu3)
      q2'v (cong-Σ≡ f2 g2 H2' Hu2')
      (Σ≡ {P = P'} (H2 ∙ cong f3 H3) Hu23)
      (∙-Σ≡ {P = P'} H2 Hu2 (cong f3 H3) mg3)
      (Σ≡ {P = P'} (cong f2 H2' ∙ H3') Hu23')
      (∙-Σ≡ {P = P'} (cong f2 H2') mg2 H3' Hu3')
      (Σ≡ {P = P'} (cong f1 H1 ∙ (H2 ∙ cong f3 H3)) UL)
      (∙-Σ≡ {P = P'} (cong f1 H1) mg1 (H2 ∙ cong f3 H3) Hu23)
      (Σ≡ {P = P'} (H1' ∙ (cong f2 H2' ∙ H3')) UR)
      (∙-Σ≡ {P = P'} H1' Hu1' (cong f2 H2' ∙ H3') Hu23')
      (Σ≡-cong2 {P = P'} {p = cong f1 H1 ∙ (H2 ∙ cong f3 H3)}
                {p' = H1' ∙ (cong f2 H2' ∙ H3')}
                {q = UL} {q' = UR} HH HHu)
      HHv


------------------------------------------------------------------------
-- Helpers of the permutahedron paste below (homotopy naturality, the
-- distributed cong of a three-factor composite, the three-square
-- zig-zag, right cancellation as a J, and the two conjugation cells
-- that the frame hexagons contribute).
------------------------------------------------------------------------

-- Homotopy naturality: a fiberwise family of paths is natural.
hnat : {A : Set ℓ} {B : Set ℓ'} {f g : A → B} (H : (a : A) → f a ≡ g a)
       {a a' : A} (ρ : a ≡ a') → cong f ρ ∙ H a' ≡ H a ∙ cong g ρ
hnat {f = f} {g = g} H {a = a} ρ =
  J (λ a' ρ → cong f ρ ∙ H a' ≡ H a ∙ cong g ρ)
    (sym (lUnit (H a)) ∙ rUnit (H a))
    ρ

-- cong of a three-factor composite, distributed.
cong-tri : {A : Set ℓ} {B : Set ℓ'} (f : A → B) {a b c d : A}
           (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
           → cong f (p ∙ (q ∙ r)) ≡ cong f p ∙ (cong f q ∙ cong f r)
cong-tri f p q r = cong-∙ f p (q ∙ r) ∙ cong (cong f p ∙_) (cong-∙ f q r)

-- Three squares pasted into one triangle.
zig3 : {a₀ a₁ a₂ a₃ r₀ r₁ r₂ r₃ : A}
       (α : a₀ ≡ r₀) (β : a₁ ≡ r₁) (γ : a₂ ≡ r₂) (δ : a₃ ≡ r₃)
       (Kx : a₀ ≡ a₁) (Ky : a₁ ≡ a₂) (Kz : a₂ ≡ a₃)
       (E1 : r₀ ≡ r₁) (E2 : r₁ ≡ r₂) (E3 : r₂ ≡ r₃)
       (A1 : α ∙ E1 ≡ Kx ∙ β) (A2 : β ∙ E2 ≡ Ky ∙ γ) (A3 : γ ∙ E3 ≡ Kz ∙ δ)
       → α ∙ (E1 ∙ (E2 ∙ E3)) ≡ (Kx ∙ (Ky ∙ Kz)) ∙ δ
zig3 α β γ δ Kx Ky Kz E1 E2 E3 A1 A2 A3 =
    sym (∙-assoc α E1 (E2 ∙ E3))
  ∙ cong (_∙ (E2 ∙ E3)) A1
  ∙ ∙-assoc Kx β (E2 ∙ E3)
  ∙ cong (Kx ∙_) ( sym (∙-assoc β E2 E3)
                 ∙ cong (_∙ E3) A2
                 ∙ ∙-assoc Ky γ E3
                 ∙ cong (Ky ∙_) A3
                 ∙ sym (∙-assoc Ky Kz δ) )
  ∙ sym (∙-assoc Kx (Ky ∙ Kz) δ)

∙-cancel-rʲ : {x y z : A} (δ : y ≡ z) {X Y : x ≡ y} → X ∙ δ ≡ Y ∙ δ → X ≡ Y
∙-cancel-rʲ {x = x} {y = y} δ =
  J (λ _ δ → {X Y : x ≡ y} → X ∙ δ ≡ Y ∙ δ → X ≡ Y)
    (λ {X} {Y} E → rUnit X ∙ (E ∙ sym (rUnit Y)))
    δ

-- The base cell of a K-edge (A2/A4/A6 of the paste below; the fiber
-- square over it is k-edge-Sq).
k-cell :
  {X2 : Set ℓ} {X0 : Set ℓ'} {f g : X2 → X0}
  (KA : (z : X2) → f z ≡ g z) {z1 z2 : X2} (pI : z1 ≡ z2)
  {y y' w v : X0}
  (Q1 : f z2 ≡ y) (gu : y ≡ y') (E : y' ≡ w) (Q2 : g z2 ≡ v) (gv : v ≡ w)
  (HH : Q1 ∙ (gu ∙ E) ≡ KA z2 ∙ (Q2 ∙ gv))
  → (cong f pI ∙ (Q1 ∙ gu)) ∙ E ≡ KA z1 ∙ (cong g pI ∙ (Q2 ∙ gv))
k-cell {f = f} {g = g} KA {z1 = z1} {z2 = z2} pI Q1 gu E Q2 gv HH =
    ∙-assoc (cong f pI) (Q1 ∙ gu) E
  ∙ ( cong (cong f pI ∙_) (∙-assoc Q1 gu E)
    ∙ ( cong (cong f pI ∙_) (refl ∙ HH)
      ∙ ( sym (∙-assoc (cong f pI) (KA z2) (Q2 ∙ gv))
        ∙ ( cong (_∙ (Q2 ∙ gv)) (refl ∙ hnat KA pI)
          ∙ ( ∙-assoc (KA z1) (cong g pI) (Q2 ∙ gv)
            ∙ refl )))))

-- The base cell of a MAP-edge (A1/A3/A5 of the paste below; the fiber
-- square over it is map-edge-Sq).
map-cell :
  {X2 : Set ℓ} {X1 : Set ℓ'} {X0 : Set ℓ''} {TU : Set ℓ'''} {T : Set ℓq}
  {rur rus : X2 → X1} {uf0 : TU → X1} {rf : X1 → X0} {rf0 : T → X0}
  {fX : TU → T}
  (g : (dd : TU) → rf (uf0 dd) ≡ rf0 (fX dd))
  {zs1 zs2 zr1 zr2 : X2} (pIs : zs1 ≡ zs2) (pIr : zr1 ≡ zr2)
  {u0 u1 : TU} (eU : u0 ≡ u1)
  (pV0 : rur zs2 ≡ uf0 u0) (pV1 : rus zr2 ≡ uf0 u1)
  (K : rur zs1 ≡ rus zr1)
  (HH : cong rur pIs ∙ (pV0 ∙ cong uf0 eU) ≡ K ∙ (cong rus pIr ∙ pV1))
  → (cong rf (cong rur pIs) ∙ (cong rf pV0 ∙ g u0))
    ∙ cong (λ dd → rf0 (fX dd)) eU
    ≡ cong rf K ∙ (cong rf (cong rus pIr) ∙ (cong rf pV1 ∙ g u1))
map-cell {rur = rur} {rus = rus} {uf0 = uf0} {rf = rf} {rf0 = rf0} {fX = fX}
         g pIs pIr eU pV0 pV1 K HH =
  c1 ∙ (c2 ∙ (c3 ∙ (c4 ∙ (c5 ∙ (c6 ∙ (c7 ∙ (c8 ∙ (c9 ∙ (c10 ∙ (c11 ∙ (c12 ∙ c13)))))))))))
  where
  α₀ : _
  α₀ = cong rf (cong rur pIs)

  EA : _
  EA = cong (λ dd → rf0 (fX dd)) eU

  uf0b : _
  uf0b = cong (λ dd → rf (uf0 dd)) eU

  c1 : _
  c1 = ∙-assoc α₀ (cong rf pV0 ∙ g _) EA

  c2 : _
  c2 = cong (α₀ ∙_) (∙-assoc (cong rf pV0) (g _) EA)

  c3 : _
  c3 = cong (α₀ ∙_)
            (cong (cong rf pV0 ∙_)
                  (sym (hnat {f = λ dd → rf (uf0 dd)}
                             {g = λ dd → rf0 (fX dd)} g eU)))

  c4 : _
  c4 = cong (α₀ ∙_) (sym (∙-assoc (cong rf pV0) uf0b (g _)))

  c5 : _
  c5 = cong (α₀ ∙_) (cong (_∙ g _) (sym (cong-∙ rf pV0 (cong uf0 eU))))

  c6 : _
  c6 = sym (∙-assoc α₀ (cong rf (pV0 ∙ cong uf0 eU)) (g _))

  c7 : _
  c7 = cong (_∙ g _) (sym (cong-∙ rf (cong rur pIs) (pV0 ∙ cong uf0 eU)))

  c8 : _
  c8 = refl

  c9 : _
  c9 = cong (_∙ g _) (cong (cong rf) HH)

  c10 : _
  c10 = cong (_∙ g _) (cong-∙ rf K (cong rus pIr ∙ pV1))

  c11 : _
  c11 = cong (_∙ g _) (cong (cong rf K ∙_) (cong-∙ rf (cong rus pIr) pV1))

  c12 : _
  c12 = ∙-assoc (cong rf K) (cong rf (cong rus pIr) ∙ cong rf pV1) (g _)

  c13 : _
  c13 = cong (cong rf K ∙_)
             (∙-assoc (cong rf (cong rus pIr)) (cong rf pV1) (g _))

------------------------------------------------------------------------
-- The permutahedral coherence of frames (νGpd/Lemmas.v):
-- the hexagon proved as a composition of the seven other hexagons of
-- the permutahedron.  Statement mirrors Rocq 1:1 (section context as
-- implicit arguments); the proof is the explicit paste.
--
-- The six squares that "hold by naturality and don't appear here
-- explicitly" (Rocq's comment) are the six hnat instances; the seven
-- given hexagons enter as six conjugation squares A1…A6 and the base
-- cell κ.  Writing (in X0)
--
--   α = image of pIs/pV0/gq u0 : rfq (rur zs1) ≡ rf0 (fA u0)
--   β = image of pIr/pV1/gq u1 : rfq (rus zr1) ≡ rf0 (fA u1)
--   γ = image of pIr/pV2/gs u2 : rfs (ruq1 zr1) ≡ rf0 (fB u2)
--   δ = image of pIq/pV3/gs u3 : rfs (rur1 zq1) ≡ rf0 (fB u3)
--   ε = image of pIs/pV4/gr u4 : rfr (ruq1 zs1) ≡ rf0 (fC u4)
--   ζ = image of pIq/pV5/gr u5 : rfr (rus zq1) ≡ rf0 (fC u5)
--
-- HH1/HH3/HH5 (pushed along rfq/rfs/rfr, closed with the naturality of
-- gq/gs/gr) give A1 : α ∙ EA ≡ cong rfq K1 ∙ β, A3, A5 (map-cell);
-- HH2/HH4/HH6 (closed with the naturality of KA2/KA4/KA6 in z) give
-- A2, A4, A6 (k-cell).  zig3 pastes three such squares into one
-- triangle, cong rf0 κ identifies the two triangles' long sides, and δ
-- cancels on the right.  A1…A6 are spelled so that the fiber squares
-- of rew-coh2Layer below paste over LITERALLY these cells.
------------------------------------------------------------------------

permutahedral-coherence :
  {X2 : Set ℓ} {X1 : Set ℓ'} {X0 : Set ℓ''}
  {TU : Set ℓ'''} {T : Set ℓp}
  {uf0 : TU → X1} {rf0 : T → X0} {fA fB fC : TU → T}
  {rfq rfs rfr : X1 → X0}
  {gq : (dd : TU) → rfq (uf0 dd) ≡ rf0 (fA dd)}
  {gs : (dd : TU) → rfs (uf0 dd) ≡ rf0 (fB dd)}
  {gr : (dd : TU) → rfr (uf0 dd) ≡ rf0 (fC dd)}
  {rur rus ruq1 rur1 : X2 → X1}
  {KA2 : (z : X2) → rfq (rus z) ≡ rfs (ruq1 z)}
  {KA4 : (z : X2) → rfq (rur z) ≡ rfr (ruq1 z)}
  {KA6 : (z : X2) → rfr (rus z) ≡ rfs (rur1 z)}
  (u0 u1 u2 u3 u4 u5 : TU)
  (eU1 : u0 ≡ u1) (eU2 : u2 ≡ u3) (eU3 : u4 ≡ u5)
  (e2 : fA u1 ≡ fB u2) (e4 : fA u0 ≡ fC u4) (e6 : fC u5 ≡ fB u3)
  (zs1 zs2 zr1 zr2 zq1 zq2 : X2)
  (pIs : zs1 ≡ zs2) (pIr : zr1 ≡ zr2) (pIq : zq1 ≡ zq2)
  (pV0 : rur zs2 ≡ uf0 u0) (pV1 : rus zr2 ≡ uf0 u1)
  (pV2 : ruq1 zr2 ≡ uf0 u2) (pV3 : rur1 zq2 ≡ uf0 u3)
  (pV4 : ruq1 zs2 ≡ uf0 u4) (pV5 : rus zq2 ≡ uf0 u5)
  (K1 : rur zs1 ≡ rus zr1) (K3 : ruq1 zr1 ≡ rur1 zq1)
  (K5 : ruq1 zs1 ≡ rus zq1)
  (HH1 : cong rur pIs ∙ (pV0 ∙ cong uf0 eU1)
         ≡ K1 ∙ (cong rus pIr ∙ pV1))
  (HH3 : cong ruq1 pIr ∙ (pV2 ∙ cong uf0 eU2)
         ≡ K3 ∙ (cong rur1 pIq ∙ pV3))
  (HH5 : cong ruq1 pIs ∙ (pV4 ∙ cong uf0 eU3)
         ≡ K5 ∙ (cong rus pIq ∙ pV5))
  (HH2 : cong rfq pV1 ∙ (gq u1 ∙ cong rf0 e2)
         ≡ KA2 zr2 ∙ (cong rfs pV2 ∙ gs u2))
  (HH4 : cong rfq pV0 ∙ (gq u0 ∙ cong rf0 e4)
         ≡ KA4 zs2 ∙ (cong rfr pV4 ∙ gr u4))
  (HH6 : cong rfr pV5 ∙ (gr u5 ∙ cong rf0 e6)
         ≡ KA6 zq2 ∙ (cong rfs pV3 ∙ gs u3))
  (κ : cong fA eU1 ∙ (e2 ∙ cong fB eU2)
       ≡ e4 ∙ (cong fC eU3 ∙ e6))
  → cong rfq K1 ∙ (KA2 zr1 ∙ cong rfs K3)
    ≡ KA4 zs1 ∙ (cong rfr K5 ∙ KA6 zq1)
permutahedral-coherence
  {uf0 = uf0} {rf0 = rf0} {fA = fA} {fB = fB} {fC = fC}
  {rfq = rfq} {rfs = rfs} {rfr = rfr}
  {gq = gq} {gs = gs} {gr = gr}
  {rur = rur} {rus = rus} {ruq1 = ruq1} {rur1 = rur1}
  {KA2 = KA2} {KA4 = KA4} {KA6 = KA6}
  u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6
  zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq
  pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5
  HH1 HH3 HH5 HH2 HH4 HH6 κ =
  ∙-cancel-rʲ δ
    ( sym (zig3 α β γ δ (cong rfq K1) (KA2 zr1) (cong rfs K3) EA E2' EB
                A1 A2 A3)
    ∙ cong (α ∙_) Kap
    ∙ zig3 α ε ζ δ (KA4 zs1) (cong rfr K5) (KA6 zq1) E4' EC E6'
           A4 A5 A6 )
  where
  α : rfq (rur zs1) ≡ rf0 (fA u0)
  α = cong rfq (cong rur pIs) ∙ (cong rfq pV0 ∙ gq u0)

  β : rfq (rus zr1) ≡ rf0 (fA u1)
  β = cong rfq (cong rus pIr) ∙ (cong rfq pV1 ∙ gq u1)

  γ : rfs (ruq1 zr1) ≡ rf0 (fB u2)
  γ = cong rfs (cong ruq1 pIr) ∙ (cong rfs pV2 ∙ gs u2)

  δ : rfs (rur1 zq1) ≡ rf0 (fB u3)
  δ = cong rfs (cong rur1 pIq) ∙ (cong rfs pV3 ∙ gs u3)

  ε : rfr (ruq1 zs1) ≡ rf0 (fC u4)
  ε = cong rfr (cong ruq1 pIs) ∙ (cong rfr pV4 ∙ gr u4)

  ζ : rfr (rus zq1) ≡ rf0 (fC u5)
  ζ = cong rfr (cong rus pIq) ∙ (cong rfr pV5 ∙ gr u5)

  EA : rf0 (fA u0) ≡ rf0 (fA u1)
  EA = cong (λ dd → rf0 (fA dd)) eU1

  EB : rf0 (fB u2) ≡ rf0 (fB u3)
  EB = cong (λ dd → rf0 (fB dd)) eU2

  EC : rf0 (fC u4) ≡ rf0 (fC u5)
  EC = cong (λ dd → rf0 (fC dd)) eU3

  E2' : rf0 (fA u1) ≡ rf0 (fB u2)
  E2' = cong rf0 e2

  E4' : rf0 (fA u0) ≡ rf0 (fC u4)
  E4' = cong rf0 e4

  E6' : rf0 (fC u5) ≡ rf0 (fB u3)
  E6' = cong rf0 e6

  A1 : α ∙ EA ≡ cong rfq K1 ∙ β
  A1 = map-cell {rur = rur} {rus = rus} {uf0 = uf0} {rf = rfq} {rf0 = rf0}
                {fX = fA} gq pIs pIr eU1 pV0 pV1 K1 HH1

  A2 : β ∙ E2' ≡ KA2 zr1 ∙ γ
  A2 = k-cell {f = λ z → rfq (rus z)} {g = λ z → rfs (ruq1 z)}
              KA2 pIr (cong rfq pV1) (gq u1) (cong rf0 e2)
              (cong rfs pV2) (gs u2) HH2

  A3 : γ ∙ EB ≡ cong rfs K3 ∙ δ
  A3 = map-cell {rur = ruq1} {rus = rur1} {uf0 = uf0} {rf = rfs} {rf0 = rf0}
                {fX = fB} gs pIr pIq eU2 pV2 pV3 K3 HH3

  A4 : α ∙ E4' ≡ KA4 zs1 ∙ ε
  A4 = k-cell {f = λ z → rfq (rur z)} {g = λ z → rfr (ruq1 z)}
                KA4 pIs (cong rfq pV0) (gq u0) (cong rf0 e4)
                (cong rfr pV4) (gr u4) HH4

  A5 : ε ∙ EC ≡ cong rfr K5 ∙ ζ
  A5 = map-cell {rur = ruq1} {rus = rus} {uf0 = uf0} {rf = rfr} {rf0 = rf0}
                {fX = fC} gr pIs pIq eU3 pV4 pV5 K5 HH5

  A6 : ζ ∙ E6' ≡ KA6 zq1 ∙ δ
  A6 = k-cell {f = λ z → rfr (rus z)} {g = λ z → rfs (rur1 z)}
                KA6 pIq (cong rfr pV5) (gr u5) (cong rf0 e6)
                (cong rfs pV3) (gs u3) HH6

  Kap : EA ∙ (E2' ∙ EB) ≡ E4' ∙ (EC ∙ E6')
  Kap = sym (cong-tri rf0 (cong fA eU1) e2 (cong fB eU2))
        ∙ cong (cong rf0) κ
        ∙ cong-tri rf0 e4 (cong fC eU3) e6
------------------------------------------------------------------------
-- rew_coh2Painting_restr0 (νGpd/Lemmas.v:449-494): statement, ported
-- 1:1 as a typechecked Set-valued definition.
--
-- The proof is rew-coh2Painting-restr0 below (a specialisation of
-- rew-coh2Painting-restr0-gen, which allows rq, rr and r0 to have
-- three different domains, as rew-cohLayer33 does).  Rocq destructs
-- everything and closes by reflexivity; here the goal is flipped by
-- substInPathL into L ≡ cong (λ e → subst P e u) κ ∙ R and the two
-- sides are shown equal by path algebra.
------------------------------------------------------------------------

rew-coh2Painting-restr0-Type :
  {TU : Set ℓ} {TL : Set ℓ'} {A0 : Set ℓ''}
  {P : TL → Set ℓ'''} {S : TU → Set ℓ'''}
  {rq rr r0 : TU → TL}
  (F : (m : TU) → S m → P (rq m))
  (G : (n : TU) → S n → P (rr n))
  {d1 d2 : TU} (E1 : d1 ≡ d2)
  {m1 m2 : TU} (e2 : m1 ≡ m2)
  {n1 n2 : TU} (e5 : n1 ≡ n2)
  (pQ : rq m2 ≡ r0 d1) (pR : rr n2 ≡ r0 d2)
  (KA : rq m1 ≡ rr n1)
  (a0 : A0) (AR : A0 → S m1) (AQ1 : A0 → S n1)
  (HK : subst P KA (F m1 (AR a0)) ≡ G n1 (AQ1 a0))
  (κ : cong rq e2 ∙ (pQ ∙ cong r0 E1) ≡ KA ∙ (cong rr e5 ∙ pR))
  (u1 : S m2) (kF : u1 ≡ subst S e2 (AR a0))
  (u12 : S n2) (kG : u12 ≡ subst S e5 (AQ1 a0))
  (w3 : P (r0 d1)) (kM : w3 ≡ subst P pQ (F m2 u1))
  (w4 : P (r0 d2)) (kM' : w4 ≡ subst P pR (G n2 u12))
  → Set ℓ'''
rew-coh2Painting-restr0-Type {P = P} {S = S} {rq = rq} {rr = rr} {r0 = r0}
  F G {d1} {d2} E1 {m1} {m2} e2 {n1} {n2} e5 pQ pR KA a0 AR AQ1 HK κ
  u1 kF u12 kG w3 kM w4 kM' =
  subst (λ π → subst P π (F m1 (AR a0)) ≡ w4) κ
    (_⊙_ {P = P} {p = cong rq e2}
         (sigT-map-eq {P = S} {Q = P} {f = rq} F {p = e2} (sym kF))
         {p' = pQ ∙ cong r0 E1}
         (_⊙_ {P = P} {p = pQ} (sym kM) {p' = cong r0 E1}
              (sym (rew-map P r0 E1 w3)
               ∙ (cong (λ x → subst (λ dd → P (r0 dd)) E1 x) kM
                  ∙ (cong (λ x → subst (λ dd → P (r0 dd)) E1
                                       (subst P pQ (F m2 x))) kF
                     ∙ (rew-cohLayer33 {P = P} {S2 = S} {S3 = S}
                          {rf0 = r0} {rfF = rq} {rfG = rr} {F = F} {G = G}
                          {E1 = E1} {C2 = e2} {D2 = e5} {C1 = pQ} {D1 = pR}
                          {K = KA} {aL = AR a0} {aR = AQ1 a0} HK κ
                        ∙ (sym (cong (λ x → subst P pR (G n2 x)) kG)
                           ∙ sym kM')))))))
  ≡ _⊙_ {P = P} {p = KA} HK {p' = cong rr e5 ∙ pR}
        (_⊙_ {P = P} {p = cong rr e5}
             (sigT-map-eq {P = S} {Q = P} {f = rr} G {p = e5} (sym kG))
             {p' = pR} (sym kM'))

------------------------------------------------------------------------
-- rew_coh2Layer (νGpd/Lemmas.v:253-445): statement, ported 1:1 as a
-- typechecked Set-valued definition (section context as implicit
-- arguments, in declaration order).
--
-- The proof is rew-coh2Layer below: the goal is flipped into a fiber
-- square (Sq) over κ, the six edges are pasted with zig3-Sq exactly as
-- permutahedral-coherence pastes its six base squares, Hcoh2Painting
-- joins the two triangles and Hcoh3Frame identifies the base cell.
------------------------------------------------------------------------

rew-coh2Layer-Type :
  {X2 : Set ℓ} {X1 : Set ℓ'} {X0 : Set ℓ''}
  {S2 : X2 → Set ℓp} {S1 : X1 → Set ℓp} {S0 : X0 → Set ℓp}
  {TU : Set ℓ'''} {T : Set ℓq}
  {uf0 : TU → X1} {rf0 : T → X0}
  {fA fB fC : TU → T}
  {rfq rfs rfr : X1 → X0}
  {Fq : (y : X1) → S1 y → S0 (rfq y)}
  {Fs : (y : X1) → S1 y → S0 (rfs y)}
  {Fr : (y : X1) → S1 y → S0 (rfr y)}
  {gq : (dd : TU) → rfq (uf0 dd) ≡ rf0 (fA dd)}
  {gs : (dd : TU) → rfs (uf0 dd) ≡ rf0 (fB dd)}
  {gr : (dd : TU) → rfr (uf0 dd) ≡ rf0 (fC dd)}
  {rur rus ruq1 rur1 : X2 → X1}
  {Rr : (z : X2) → S2 z → S1 (rur z)}
  {Rs : (z : X2) → S2 z → S1 (rus z)}
  {Rq1 : (z : X2) → S2 z → S1 (ruq1 z)}
  {Rr1 : (z : X2) → S2 z → S1 (rur1 z)}
  {KA2 : (z : X2) → rfq (rus z) ≡ rfs (ruq1 z)}
  {KA4 : (z : X2) → rfq (rur z) ≡ rfr (ruq1 z)}
  {KA6 : (z : X2) → rfr (rus z) ≡ rfs (rur1 z)}
  {HKA2 : (z : X2) (c : S2 z)
          → subst S0 (KA2 z) (Fq (rus z) (Rs z c)) ≡ Fs (ruq1 z) (Rq1 z c)}
  {HKA4 : (z : X2) (c : S2 z)
          → subst S0 (KA4 z) (Fq (rur z) (Rr z c)) ≡ Fr (ruq1 z) (Rq1 z c)}
  {HKA6 : (z : X2) (c : S2 z)
          → subst S0 (KA6 z) (Fr (rus z) (Rs z c)) ≡ Fs (rur1 z) (Rr1 z c)}
  {A0 : Set ℓr} {a : A0}
  (u0 u1 u2 u3 u4 u5 : TU)
  (eU1 : u0 ≡ u1) (eU2 : u2 ≡ u3) (eU3 : u4 ≡ u5)
  (e2 : fA u1 ≡ fB u2) (e4 : fA u0 ≡ fC u4) (e6 : fC u5 ≡ fB u3)
  (zs1 zs2 zr1 zr2 zq1 zq2 : X2)
  (pIs : zs1 ≡ zs2) (pIr : zr1 ≡ zr2) (pIq : zq1 ≡ zq2)
  (FIs : A0 → S2 zs1) (FIr : A0 → S2 zr1) (FIq : A0 → S2 zq1)
  (pV0 : rur zs2 ≡ uf0 u0) (pV1 : rus zr2 ≡ uf0 u1)
  (pV2 : ruq1 zr2 ≡ uf0 u2) (pV3 : rur1 zq2 ≡ uf0 u3)
  (pV4 : ruq1 zs2 ≡ uf0 u4) (pV5 : rus zq2 ≡ uf0 u5)
  (K1 : rur zs1 ≡ rus zr1) (K3 : ruq1 zr1 ≡ rur1 zq1)
  (K5 : ruq1 zs1 ≡ rus zq1)
  (HK1 : subst S1 K1 (Rr zs1 (FIs a)) ≡ Rs zr1 (FIr a))
  (HK3 : subst S1 K3 (Rq1 zr1 (FIr a)) ≡ Rr1 zq1 (FIq a))
  (HK5 : subst S1 K5 (Rq1 zs1 (FIs a)) ≡ Rs zq1 (FIq a))
  (HH1 : cong rur pIs ∙ (pV0 ∙ cong uf0 eU1)
         ≡ K1 ∙ (cong rus pIr ∙ pV1))
  (HH3 : cong ruq1 pIr ∙ (pV2 ∙ cong uf0 eU2)
         ≡ K3 ∙ (cong rur1 pIq ∙ pV3))
  (HH5 : cong ruq1 pIs ∙ (pV4 ∙ cong uf0 eU3)
         ≡ K5 ∙ (cong rus pIq ∙ pV5))
  (HH2 : cong rfq pV1 ∙ (gq u1 ∙ cong rf0 e2)
         ≡ KA2 zr2 ∙ (cong rfs pV2 ∙ gs u2))
  (HH4 : cong rfq pV0 ∙ (gq u0 ∙ cong rf0 e4)
         ≡ KA4 zs2 ∙ (cong rfr pV4 ∙ gr u4))
  (HH6 : cong rfr pV5 ∙ (gr u5 ∙ cong rf0 e6)
         ≡ KA6 zq2 ∙ (cong rfs pV3 ∙ gs u3))
  (aP : S2 zs2) (kP : aP ≡ subst S2 pIs (FIs a))
  (aQ : S2 zr2) (kQ : aQ ≡ subst S2 pIr (FIr a))
  (aR : S2 zq2) (kR : aR ≡ subst S2 pIq (FIq a))
  (bP : S1 (uf0 u0)) (kbP : bP ≡ subst S1 pV0 (Rr zs2 aP))
  (bQ : S1 (uf0 u1)) (kbQ : bQ ≡ subst S1 pV1 (Rs zr2 aQ))
  (bR : S1 (uf0 u2)) (kbR : bR ≡ subst S1 pV2 (Rq1 zr2 aQ))
  (bR' : S1 (uf0 u3)) (kbR' : bR' ≡ subst S1 pV3 (Rr1 zq2 aR))
  (bW : S1 (uf0 u4)) (kbW : bW ≡ subst S1 pV4 (Rq1 zs2 aP))
  (bW' : S1 (uf0 u5)) (kbW' : bW' ≡ subst S1 pV5 (Rs zq2 aR))
  (cA0 : S0 (rf0 (fA u0))) (kc0 : cA0 ≡ subst S0 (gq u0) (Fq (uf0 u0) bP))
  (cA1 : S0 (rf0 (fA u1))) (kc1 : cA1 ≡ subst S0 (gq u1) (Fq (uf0 u1) bQ))
  (cB2 : S0 (rf0 (fB u2))) (kc2 : cB2 ≡ subst S0 (gs u2) (Fs (uf0 u2) bR))
  (cB3 : S0 (rf0 (fB u3))) (kc3 : cB3 ≡ subst S0 (gs u3) (Fs (uf0 u3) bR'))
  (cC4 : S0 (rf0 (fC u4))) (kc4 : cC4 ≡ subst S0 (gr u4) (Fr (uf0 u4) bW))
  (cC5 : S0 (rf0 (fC u5))) (kc5 : cC5 ≡ subst S0 (gr u5) (Fr (uf0 u5) bW'))
  (κ : cong fA eU1 ∙ (e2 ∙ cong fB eU2) ≡ e4 ∙ (cong fC eU3 ∙ e6))
  (HHA : cong rfq K1 ∙ (KA2 zr1 ∙ cong rfs K3)
         ≡ KA4 zs1 ∙ (cong rfr K5 ∙ KA6 zq1))
  (Hcoh2Painting :
    subst (λ π → subst S0 π (Fq (rur zs1) (Rr zs1 (FIs a)))
                 ≡ Fs (rur1 zq1) (Rr1 zq1 (FIq a))) HHA
      (_⊙_ {P = S0} {p = cong rfq K1}
           (sigT-map-eq {P = S1} {Q = S0} {f = rfq} Fq {p = K1} HK1)
           {p' = KA2 zr1 ∙ cong rfs K3}
           (_⊙_ {P = S0} {p = KA2 zr1} (HKA2 zr1 (FIr a))
                {p' = cong rfs K3}
                (sigT-map-eq {P = S1} {Q = S0} {f = rfs} Fs {p = K3} HK3)))
    ≡ _⊙_ {P = S0} {p = KA4 zs1} (HKA4 zs1 (FIs a))
          {p' = cong rfr K5 ∙ KA6 zq1}
          (_⊙_ {P = S0} {p = cong rfr K5}
               (sigT-map-eq {P = S1} {Q = S0} {f = rfr} Fr {p = K5} HK5)
               {p' = KA6 zq1} (HKA6 zq1 (FIq a))))
  (Hcoh3Frame :
    HHA ≡ permutahedral-coherence {uf0 = uf0} {rf0 = rf0}
            {fA = fA} {fB = fB} {fC = fC}
            {rfq = rfq} {rfs = rfs} {rfr = rfr}
            {gq = gq} {gs = gs} {gr = gr}
            {rur = rur} {rus = rus} {ruq1 = ruq1} {rur1 = rur1}
            {KA2 = KA2} {KA4 = KA4} {KA6 = KA6}
            u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6
            zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq
            pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5
            HH1 HH3 HH5 HH2 HH4 HH6 κ)
  → Set ℓp
rew-coh2Layer-Type
  {X2 = X2} {X1 = X1} {X0 = X0} {S2 = S2} {S1 = S1} {S0 = S0}
  {TU = TU} {T = T} {uf0 = uf0} {rf0 = rf0}
  {fA = fA} {fB = fB} {fC = fC} {rfq = rfq} {rfs = rfs} {rfr = rfr}
  {Fq = Fq} {Fs = Fs} {Fr = Fr} {gq = gq} {gs = gs} {gr = gr}
  {rur = rur} {rus = rus} {ruq1 = ruq1} {rur1 = rur1}
  {Rr = Rr} {Rs = Rs} {Rq1 = Rq1} {Rr1 = Rr1}
  {KA2 = KA2} {KA4 = KA4} {KA6 = KA6}
  {HKA2 = HKA2} {HKA4 = HKA4} {HKA6 = HKA6} {A0 = A0} {a = a}
  u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6
  zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq FIs FIr FIq
  pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5 HK1 HK3 HK5
  HH1 HH3 HH5 HH2 HH4 HH6
  aP kP aQ kQ aR kR bP kbP bQ kbQ bR kbR bR' kbR' bW kbW bW' kbW'
  cA0 kc0 cA1 kc1 cB2 kc2 cB3 kc3 cC4 kc4 cC5 kc5
  κ HHA Hcoh2Painting Hcoh3Frame =
  subst (λ e → subst S0r e cA0 ≡ cB3) κ
    (_⊙_ {P = S0r} {p = cong fA eU1} C1comp
         {p' = e2 ∙ cong fB eU2}
         (_⊙_ {P = S0r} {p = e2} C2comp {p' = cong fB eU2} C3comp))
  ≡ _⊙_ {P = S0r} {p = e4} C4comp
        {p' = cong fC eU3 ∙ e6}
        (_⊙_ {P = S0r} {p = cong fC eU3} C5comp {p' = e6} C6comp)
  where
  S0r : T → Set _
  S0r dd = S0 (rf0 dd)

  S1u : TU → Set _
  S1u dd = S1 (uf0 dd)

  C1comp : subst S0r (cong fA eU1) cA0 ≡ cA1
  C1comp =
    cong (λ x → subst S0r (cong fA eU1) x) kc0
    ∙ (sigT-map-eq {P = S1u} {Q = S0r} {f = fA}
         (λ dd x → subst S0 (gq dd) (Fq (uf0 dd) x)) {p = eU1}
         (cong (λ x → subst S1u eU1 x) kbP
          ∙ (cong (λ x → subst S1u eU1 (subst S1 pV0 (Rr zs2 x))) kP
             ∙ (rew-cohLayer33 {P = S1} {S2 = S2} {S3 = S2}
                  {rf0 = uf0} {rfF = rur} {rfG = rus} {F = Rr} {G = Rs}
                  {E1 = eU1} {C2 = pIs} {D2 = pIr} {C1 = pV0} {D1 = pV1}
                  {K = K1} {aL = FIs a} {aR = FIr a} HK1 HH1
                ∙ (sym (cong (λ x → subst S1 pV1 (Rs zr2 x)) kQ)
                   ∙ sym kbQ))))
       ∙ sym kc1)

  C2comp : subst S0r e2 cA1 ≡ cB2
  C2comp =
    cong (λ x → subst S0r e2 x) kc1
    ∙ (cong (λ x → subst S0r e2 (subst S0 (gq u1) (Fq (uf0 u1) x))) kbQ
       ∙ (rew-cohLayer33 {P = S0} {S2 = S1} {S3 = S1}
            {rf0 = rf0} {rfF = rfq} {rfG = rfs} {F = Fq} {G = Fs}
            {E1 = e2} {C2 = pV1} {D2 = pV2} {C1 = gq u1} {D1 = gs u2}
            {K = KA2 zr2} {aL = Rs zr2 aQ} {aR = Rq1 zr2 aQ}
            (HKA2 zr2 aQ) HH2
          ∙ (sym (cong (λ x → subst S0 (gs u2) (Fs (uf0 u2) x)) kbR)
             ∙ sym kc2)))

  C3comp : subst S0r (cong fB eU2) cB2 ≡ cB3
  C3comp =
    cong (λ x → subst S0r (cong fB eU2) x) kc2
    ∙ (sigT-map-eq {P = S1u} {Q = S0r} {f = fB}
         (λ dd x → subst S0 (gs dd) (Fs (uf0 dd) x)) {p = eU2}
         (cong (λ x → subst S1u eU2 x) kbR
          ∙ (cong (λ x → subst S1u eU2 (subst S1 pV2 (Rq1 zr2 x))) kQ
             ∙ (rew-cohLayer33 {P = S1} {S2 = S2} {S3 = S2}
                  {rf0 = uf0} {rfF = ruq1} {rfG = rur1} {F = Rq1} {G = Rr1}
                  {E1 = eU2} {C2 = pIr} {D2 = pIq} {C1 = pV2} {D1 = pV3}
                  {K = K3} {aL = FIr a} {aR = FIq a} HK3 HH3
                ∙ (sym (cong (λ x → subst S1 pV3 (Rr1 zq2 x)) kR)
                   ∙ sym kbR'))))
       ∙ sym kc3)

  C4comp : subst S0r e4 cA0 ≡ cC4
  C4comp =
    cong (λ x → subst S0r e4 x) kc0
    ∙ (cong (λ x → subst S0r e4 (subst S0 (gq u0) (Fq (uf0 u0) x))) kbP
       ∙ (rew-cohLayer33 {P = S0} {S2 = S1} {S3 = S1}
            {rf0 = rf0} {rfF = rfq} {rfG = rfr} {F = Fq} {G = Fr}
            {E1 = e4} {C2 = pV0} {D2 = pV4} {C1 = gq u0} {D1 = gr u4}
            {K = KA4 zs2} {aL = Rr zs2 aP} {aR = Rq1 zs2 aP}
            (HKA4 zs2 aP) HH4
          ∙ (sym (cong (λ x → subst S0 (gr u4) (Fr (uf0 u4) x)) kbW)
             ∙ sym kc4)))

  C5comp : subst S0r (cong fC eU3) cC4 ≡ cC5
  C5comp =
    cong (λ x → subst S0r (cong fC eU3) x) kc4
    ∙ (sigT-map-eq {P = S1u} {Q = S0r} {f = fC}
         (λ dd x → subst S0 (gr dd) (Fr (uf0 dd) x)) {p = eU3}
         (cong (λ x → subst S1u eU3 x) kbW
          ∙ (cong (λ x → subst S1u eU3 (subst S1 pV4 (Rq1 zs2 x))) kP
             ∙ (rew-cohLayer33 {P = S1} {S2 = S2} {S3 = S2}
                  {rf0 = uf0} {rfF = ruq1} {rfG = rus} {F = Rq1} {G = Rs}
                  {E1 = eU3} {C2 = pIs} {D2 = pIq} {C1 = pV4} {D1 = pV5}
                  {K = K5} {aL = FIs a} {aR = FIq a} HK5 HH5
                ∙ (sym (cong (λ x → subst S1 pV5 (Rs zq2 x)) kR)
                   ∙ sym kbW'))))
       ∙ sym kc5)

  C6comp : subst S0r e6 cC5 ≡ cB3
  C6comp =
    cong (λ x → subst S0r e6 x) kc5
    ∙ (cong (λ x → subst S0r e6 (subst S0 (gr u5) (Fr (uf0 u5) x))) kbW'
       ∙ (rew-cohLayer33 {P = S0} {S2 = S1} {S3 = S1}
            {rf0 = rf0} {rfF = rfr} {rfG = rfs} {F = Fr} {G = Fs}
            {E1 = e6} {C2 = pV5} {D2 = pV3} {C1 = gr u5} {D1 = gs u3}
            {K = KA6 zq2} {aL = Rs zq2 aR} {aR = Rr1 zq2 aR}
            (HKA6 zq2 aR) HH6
          ∙ (sym (cong (λ x → subst S0 (gs u3) (Fs (uf0 u3) x)) kbR')
             ∙ sym kc3)))


------------------------------------------------------------------------
-- Small path-algebra kit
------------------------------------------------------------------------


-- Right cancellation (mirror of ∙-cancel-l above).
∙-cancel-r : {x y z : A} (X : x ≡ y) (s : y ≡ z) → (X ∙ s) ∙ sym s ≡ X
∙-cancel-r X s =
  J (λ _ s → (X ∙ s) ∙ sym s ≡ X)
    (sym (rUnit (X ∙ refl)) ∙ sym (rUnit X))
    s

-- substCommSlice computes at p = refl (via JRefl).
substCommSlice-refl :
  {A : Set ℓ} {B : Set ℓ'} {S : A → Set ℓ''} {Q : B → Set ℓ'''}
  (f : A → B) (g : (a : A) → S a → Q (f a)) {m : A} (s : S m)
  → substCommSlice {S = S} {P = Q} f g refl s
    ≡ substRefl Q (g m s) ∙ cong (g m) (sym (substRefl S s))
substCommSlice-refl {S = S} {Q = Q} f g {m} s =
  JRefl (λ m2 p → subst Q (cong f p) (g m s) ≡ g m2 (subst S p s))
        (substRefl Q (g m s) ∙ cong (g m) (sym (substRefl S s)))

-- ∙-assoc computes at r = refl (via JRefl).
∙-assoc-refl : {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → ∙-assoc p q refl ≡ sym (rUnit (p ∙ q)) ∙ cong (p ∙_) (rUnit q)
∙-assoc-refl p q =
  JRefl (λ _ r → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r))
        (sym (rUnit (p ∙ q)) ∙ cong (p ∙_) (rUnit q))

------------------------------------------------------------------------
-- sigT-map-eq decomposed: the fiber equation splits off as a cong
------------------------------------------------------------------------

-- sigT-map-eq at a refl fiber equation IS substCommSlice.
sigT-map-eq-filler :
  {A : Set ℓ} {B : Set ℓ'} {S : A → Set ℓ''} {Q : B → Set ℓ'''}
  {f : A → B} (g : (a : A) → S a → Q (f a))
  {x y : A} (p : x ≡ y) (u : S x)
  → sigT-map-eq {P = S} {Q = Q} {f = f} g {p = p} (refl {x = subst S p u})
    ≡ substCommSlice {S = S} {P = Q} f g p u
sigT-map-eq-filler {S = S} {Q = Q} {f = f} g {x = x} p u =
  J (λ y p → sigT-map-eq {P = S} {Q = Q} {f = f} g {p = p}
                         (refl {x = subst S p u})
             ≡ substCommSlice {S = S} {P = Q} f g p u)
    ( sigT-map-eq-refl {P = S} {Q = Q} {f = f} g (refl {x = subst S refl u})
    ∙ cong (λ w → substRefl Q (g x u) ∙ cong (g x) w)
           (sym (rUnit (sym (substRefl S u))))
    ∙ sym (substCommSlice-refl {S = S} {Q = Q} f g u) )
    p

sigT-map-eq-decomp :
  {A : Set ℓ} {B : Set ℓ'} {S : A → Set ℓ''} {Q : B → Set ℓ'''}
  {f : A → B} (g : (a : A) → S a → Q (f a))
  {x y : A} (p : x ≡ y) {u : S x} {v : S y} (q : subst S p u ≡ v)
  → sigT-map-eq {P = S} {Q = Q} {f = f} g {p = p} q
    ≡ substCommSlice {S = S} {P = Q} f g p u ∙ cong (g y) q
sigT-map-eq-decomp {S = S} {Q = Q} {f = f} g {y = y} p {u = u} q =
  J (λ v q → sigT-map-eq {P = S} {Q = Q} {f = f} g {p = p} q
             ≡ substCommSlice {S = S} {P = Q} f g p u ∙ cong (g y) q)
    ( sigT-map-eq-filler {S = S} {Q = Q} {f = f} g p u
    ∙ rUnit (substCommSlice {S = S} {P = Q} f g p u) )
    q

------------------------------------------------------------------------
-- The associativity coherence of substComposite
------------------------------------------------------------------------

substComposite-assoc-base :
  {A : Set ℓ} (P : A → Set ℓ') {x y z : A}
  (p : x ≡ y) (q : y ≡ z) (u : P x)
  → cong (λ e → subst P e u) (∙-assoc p q refl)
    ∙ (substComposite P p (q ∙ refl) u
       ∙ substComposite P q refl (subst P p u))
    ≡ substComposite P (p ∙ q) refl u
      ∙ cong (subst P refl) (substComposite P p q u)
substComposite-assoc-base {A = A} P p q u =
    cong (λ w → w ∙ (SCpqr ∙ SCqr))
         (cong (cong (λ e → subst P e u)) (∙-assoc-refl p q)
          ∙ cong-∙ (λ e → subst P e u)
                   (sym (rUnit (p ∙ q))) (cong (p ∙_) (rUnit q)))
  ∙ cong (λ w → (sym μ ∙ ξ) ∙ (SCpqr ∙ w))
         (substComposite-refl P q Tp)
  ∙ ∙-assoc (sym μ) ξ (SCpqr ∙ (sym ν ∙ sym s2))
  ∙ cong (sym μ ∙_) inner
  ∙ cong (sym μ ∙_) (sym (∙-cancel-l s1 (SCpq ∙ sym s2)))
  ∙ sym (∙-assoc (sym μ) (sym s1) (s1 ∙ (SCpq ∙ sym s2)))
  ∙ sym (cong₂ (λ α β → α ∙ β)
               (substComposite-refl P (p ∙ q) u)
               (substRefl-natural {P = P} (substComposite P p q u)))
  where
  Tp : P _
  Tp = subst P p u

  SCpq : subst P (p ∙ q) u ≡ subst P q Tp
  SCpq = substComposite P p q u

  SCpqr : subst P (p ∙ (q ∙ refl)) u ≡ subst P (q ∙ refl) Tp
  SCpqr = substComposite P p (q ∙ refl) u

  SCqr : subst P (q ∙ refl) Tp ≡ subst P refl (subst P q Tp)
  SCqr = substComposite P q refl Tp

  μ : subst P (p ∙ q) u ≡ subst P ((p ∙ q) ∙ refl) u
  μ = cong (λ e → subst P e u) (rUnit (p ∙ q))

  ξ : subst P (p ∙ q) u ≡ subst P (p ∙ (q ∙ refl)) u
  ξ = cong (λ w → subst P (p ∙ w) u) (rUnit q)

  ν : subst P q Tp ≡ subst P (q ∙ refl) Tp
  ν = cong (λ w → subst P w Tp) (rUnit q)

  s1 : subst P refl (subst P (p ∙ q) u) ≡ subst P (p ∙ q) u
  s1 = substRefl P (subst P (p ∙ q) u)

  s2 : subst P refl (subst P q Tp) ≡ subst P q Tp
  s2 = substRefl P (subst P q Tp)

  inner : ξ ∙ (SCpqr ∙ (sym ν ∙ sym s2)) ≡ SCpq ∙ sym s2
  inner =
      sym (∙-assoc ξ SCpqr (sym ν ∙ sym s2))
    ∙ cong (λ w → w ∙ (sym ν ∙ sym s2))
           (hnat (λ w → substComposite P p w u) (rUnit q))
    ∙ ∙-assoc SCpq ν (sym ν ∙ sym s2)
    ∙ cong (SCpq ∙_) (∙-cancel-l (sym ν) (sym s2))

substComposite-assoc :
  {A : Set ℓ} (P : A → Set ℓ') {x y z w : A}
  (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (u : P x)
  → cong (λ e → subst P e u) (∙-assoc p q r)
    ∙ (substComposite P p (q ∙ r) u ∙ substComposite P q r (subst P p u))
    ≡ substComposite P (p ∙ q) r u ∙ cong (subst P r) (substComposite P p q u)
substComposite-assoc P p q r u =
  J (λ w r → cong (λ e → subst P e u) (∙-assoc p q r)
             ∙ (substComposite P p (q ∙ r) u
                ∙ substComposite P q r (subst P p u))
             ≡ substComposite P (p ∙ q) r u
               ∙ cong (subst P r) (substComposite P p q u))
    (substComposite-assoc-base P p q u)
    r

------------------------------------------------------------------------
-- Two cancellation shapes used by both proofs
------------------------------------------------------------------------

∙-cancel-mid : {x y z : A} (α : x ≡ y) (β : z ≡ y)
               → (α ∙ sym β) ∙ (β ∙ sym α) ≡ refl
∙-cancel-mid α β =
    ∙-assoc α (sym β) (β ∙ sym α)
  ∙ cong (α ∙_) (∙-cancel-l β (sym α))
  ∙ rCancel α

-- If α ∙ W is the inverse of Rz then W, Rz and α close a triangle.
cancel-triangle : {x y z : A} (α : x ≡ y) (W : y ≡ z) (Rz : z ≡ x)
                  → α ∙ W ≡ sym Rz → W ∙ (Rz ∙ α) ≡ refl
cancel-triangle α W Rz E =
    cong (_∙ (Rz ∙ α)) (sym (∙-cancel-l α W))
  ∙ cong (λ w → (sym α ∙ w) ∙ (Rz ∙ α)) E
  ∙ ∙-assoc (sym α) (sym Rz) (Rz ∙ α)
  ∙ cong (sym α ∙_) (∙-cancel-l Rz α)
  ∙ lCancel α

------------------------------------------------------------------------
-- rew_coh2Painting_restr0 (νGpd/Lemmas.v:449-494)
------------------------------------------------------------------------

rew-coh2Painting-restr0-gen :
  {T1 : Set ℓ} {T2 T3 : Set ℓ'} {X : Set ℓ''} {A0 : Set ℓq}
  {P : X → Set ℓp} {S2 : T2 → Set ℓp} {S3 : T3 → Set ℓp}
  {rq : T2 → X} {rr : T3 → X} {r0 : T1 → X}
  (F : (m : T2) → S2 m → P (rq m))
  (G : (n : T3) → S3 n → P (rr n))
  {d1 d2 : T1} (E1 : d1 ≡ d2)
  {m1 m2 : T2} (e2 : m1 ≡ m2)
  {n1 n2 : T3} (e5 : n1 ≡ n2)
  (pQ : rq m2 ≡ r0 d1) (pR : rr n2 ≡ r0 d2)
  (KA : rq m1 ≡ rr n1)
  (a0 : A0) (AR : A0 → S2 m1) (AQ1 : A0 → S3 n1)
  (HK : subst P KA (F m1 (AR a0)) ≡ G n1 (AQ1 a0))
  (κ : cong rq e2 ∙ (pQ ∙ cong r0 E1) ≡ KA ∙ (cong rr e5 ∙ pR))
  (u1 : S2 m2) (kF : u1 ≡ subst S2 e2 (AR a0))
  (u12 : S3 n2) (kG : u12 ≡ subst S3 e5 (AQ1 a0))
  (w3 : P (r0 d1)) (kM : w3 ≡ subst P pQ (F m2 u1))
  (w4 : P (r0 d2)) (kM' : w4 ≡ subst P pR (G n2 u12))
  → subst (λ π → subst P π (F m1 (AR a0)) ≡ w4) κ
      (_⊙_ {P = P} {p = cong rq e2}
           (sigT-map-eq {P = S2} {Q = P} {f = rq} F {p = e2} (sym kF))
           {p' = pQ ∙ cong r0 E1}
           (_⊙_ {P = P} {p = pQ} (sym kM) {p' = cong r0 E1}
                (sym (rew-map P r0 E1 w3)
                 ∙ (cong (λ x → subst (λ dd → P (r0 dd)) E1 x) kM
                    ∙ (cong (λ x → subst (λ dd → P (r0 dd)) E1
                                         (subst P pQ (F m2 x))) kF
                       ∙ (rew-cohLayer33 {P = P} {S2 = S2} {S3 = S3}
                            {rf0 = r0} {rfF = rq} {rfG = rr} {F = F} {G = G}
                            {E1 = E1} {C2 = e2} {D2 = e5} {C1 = pQ} {D1 = pR}
                            {K = KA} {aL = AR a0} {aR = AQ1 a0} HK κ
                          ∙ (sym (cong (λ x → subst P pR (G n2 x)) kG)
                             ∙ sym kM')))))))
    ≡ _⊙_ {P = P} {p = KA} HK {p' = cong rr e5 ∙ pR}
          (_⊙_ {P = P} {p = cong rr e5}
               (sigT-map-eq {P = S3} {Q = P} {f = rr} G {p = e5} (sym kG))
               {p' = pR} (sym kM'))
rew-coh2Painting-restr0-gen {P = P} {S2 = S2} {S3 = S3} {rq = rq} {rr = rr} {r0 = r0}
  F G {d1} {d2} E1 {m1} {m2} e2 {n1} {n2} e5 pQ pR KA a0 AR AQ1 HK κ
  u1 kF u12 kG w3 kM w4 kM' = main
  where
  aL : S2 m1
  aL = AR a0

  aQ : S3 n1
  aQ = AQ1 a0

  u : P (rq m1)
  u = F m1 aL

  c2 : rq m1 ≡ rq m2
  c2 = cong rq e2

  c5 : rr n1 ≡ rr n2
  c5 = cong rr e5

  cE : r0 d1 ≡ r0 d2
  cE = cong r0 E1

  Mu : (rq m1 ≡ r0 d2) → P (r0 d2)
  Mu e = subst P e u

  cuκ : subst P (c2 ∙ (pQ ∙ cE)) u ≡ subst P (KA ∙ (c5 ∙ pR)) u
  cuκ = cong Mu κ

  -- the fiberwise map of the two ⊙-chains
  gg : P (rq m2) → P (r0 d2)
  gg z = subst P cE (subst P pQ z)

  scsF : subst P c2 u ≡ F m2 (subst S2 e2 aL)
  scsF = substCommSlice {S = S2} {P = P} rq F e2 aL

  scsG : subst P c5 (G n1 aQ) ≡ G n2 (subst S3 e5 aQ)
  scsG = substCommSlice {S = S3} {P = P} rr G e5 aQ

  AF : subst P c2 u ≡ F m2 u1
  AF = sigT-map-eq {P = S2} {Q = P} {f = rq} F {p = e2} (sym kF)

  AG : subst P c5 (G n1 aQ) ≡ G n2 u12
  AG = sigT-map-eq {P = S3} {Q = P} {f = rr} G {p = e5} (sym kG)

  YF : F m2 u1 ≡ F m2 (subst S2 e2 aL)
  YF = cong (F m2) kF

  YG : G n2 u12 ≡ G n2 (subst S3 e5 aQ)
  YG = cong (G n2) kG

  -- the eight steps of rew-cohLayer33
  SCpq : subst P (c2 ∙ pQ) u ≡ subst P pQ (subst P c2 u)
  SCpq = substComposite P c2 pQ u

  R1 : gg (F m2 (subst S2 e2 aL)) ≡ gg (subst P c2 u)
  R1 = cong gg (sym scsF)

  R2 : gg (subst P c2 u) ≡ subst P cE (subst P (c2 ∙ pQ) u)
  R2 = cong (subst P cE) (sym SCpq)

  R3 : subst P cE (subst P (c2 ∙ pQ) u) ≡ subst P ((c2 ∙ pQ) ∙ cE) u
  R3 = sym (substComposite P (c2 ∙ pQ) cE u)

  a1 : subst P ((c2 ∙ pQ) ∙ cE) u ≡ subst P (c2 ∙ (pQ ∙ cE)) u
  a1 = cong Mu (∙-assoc c2 pQ cE)

  R4 : subst P ((c2 ∙ pQ) ∙ cE) u ≡ subst P (KA ∙ (c5 ∙ pR)) u
  R4 = cong Mu (∙-assoc c2 pQ cE ∙ κ)

  R5 : subst P (KA ∙ (c5 ∙ pR)) u ≡ subst P (c5 ∙ pR) (subst P KA u)
  R5 = substComposite P KA (c5 ∙ pR) u

  R6 : subst P (c5 ∙ pR) (subst P KA u) ≡ subst P (c5 ∙ pR) (G n1 aQ)
  R6 = cong (subst P (c5 ∙ pR)) HK

  R7 : subst P (c5 ∙ pR) (G n1 aQ) ≡ subst P pR (subst P c5 (G n1 aQ))
  R7 = substComposite P c5 pR (G n1 aQ)

  R8 : subst P pR (subst P c5 (G n1 aQ)) ≡ subst P pR (G n2 (subst S3 e5 aQ))
  R8 = cong (subst P pR) scsG

  tail : subst P pR (G n2 (subst S3 e5 aQ)) ≡ w4
  tail = sym (cong (λ x → subst P pR (G n2 x)) kG) ∙ sym kM'

  REST : gg (subst P c2 u) ≡ subst P pR (G n2 (subst S3 e5 aQ))
  REST = R2 ∙ (R3 ∙ (R4 ∙ (R5 ∙ (R6 ∙ (R7 ∙ R8)))))

  RCL : gg (F m2 (subst S2 e2 aL)) ≡ subst P pR (G n2 (subst S3 e5 aQ))
  RCL = R1 ∙ REST

  Z : gg (F m2 u1) ≡ w4
  Z = cong (λ x → subst P cE (subst P pQ (F m2 x))) kF ∙ (RCL ∙ tail)

  BIG : subst P cE w3 ≡ w4
  BIG = sym (rew-map P r0 E1 w3)
        ∙ (cong (λ x → subst (λ dd → P (r0 dd)) E1 x) kM ∙ Z)

  Lchain : subst P (c2 ∙ (pQ ∙ cE)) u ≡ w4
  Lchain = _⊙_ {P = P} {p = c2} AF {p' = pQ ∙ cE}
                (_⊙_ {P = P} {p = pQ} (sym kM) {p' = cE} BIG)

  Rchain : subst P (KA ∙ (c5 ∙ pR)) u ≡ w4
  Rchain = _⊙_ {P = P} {p = KA} HK {p' = c5 ∙ pR}
                (_⊙_ {P = P} {p = c5} AG {p' = pR} (sym kM'))

  SCa : subst P (c2 ∙ (pQ ∙ cE)) u ≡ subst P (pQ ∙ cE) (subst P c2 u)
  SCa = substComposite P c2 (pQ ∙ cE) u

  SCb : subst P (pQ ∙ cE) (F m2 u1) ≡ gg (F m2 u1)
  SCb = substComposite P pQ cE (F m2 u1)

  SCb' : subst P (pQ ∙ cE) (subst P c2 u) ≡ gg (subst P c2 u)
  SCb' = substComposite P pQ cE (subst P c2 u)

  XM : subst P cE w3 ≡ subst P cE (subst P pQ (F m2 u1))
  XM = cong (subst P cE) kM

  -- Step 1: the stored kM cancels against its own inverse inside BIG.
  step1 : cong (subst P cE) (sym kM) ∙ BIG ≡ Z
  step1 = cong (sym XM ∙_) (sym (lUnit (XM ∙ Z))) ∙ ∙-cancel-l XM Z

  -- Step 2: naturality of substComposite in its element argument.
  step2 : cong (subst P (pQ ∙ cE)) AF ∙ (SCb ∙ Z) ≡ SCb' ∙ (cong gg AF ∙ Z)
  step2 =
      sym (∙-assoc (cong (subst P (pQ ∙ cE)) AF) SCb Z)
    ∙ cong (_∙ Z) (hnat {f = λ v → subst P (pQ ∙ cE) v} {g = gg}
                        (λ v → substComposite P pQ cE v) AF)
    ∙ ∙-assoc SCb' (cong gg AF) Z

  -- Step 3: the head of rew-cohLayer33 cancels the stored kF against
  -- sigT-map-eq's substCommSlice component.
  cancelA : AF ∙ (YF ∙ sym scsF) ≡ refl
  cancelA =
      cong (_∙ (YF ∙ sym scsF))
           (sigT-map-eq-decomp {S = S2} {Q = P} {f = rq} F e2 (sym kF))
    ∙ ∙-cancel-mid scsF YF

  step3 : cong gg AF ∙ Z ≡ REST ∙ tail
  step3 =
      cong (λ w → cong gg AF ∙ (cong gg YF ∙ w)) (∙-assoc R1 REST tail)
    ∙ cong (cong gg AF ∙_)
           (sym (∙-assoc (cong gg YF) R1 (REST ∙ tail)))
    ∙ sym (∙-assoc (cong gg AF) (cong gg YF ∙ R1) (REST ∙ tail))
    ∙ cong (_∙ (REST ∙ tail))
           (sym (cong-∙ gg AF (YF ∙ sym scsF)
                 ∙ cong (cong gg AF ∙_) (cong-∙ gg YF (sym scsF))))
    ∙ cong (λ w → cong gg w ∙ (REST ∙ tail)) cancelA
    ∙ sym (lUnit (REST ∙ tail))

  -- Step 4: push the tail inside and split R4 into a1 ∙ cuκ.
  Mtail : subst P (c2 ∙ (pQ ∙ cE)) u ≡ w4
  Mtail = cuκ ∙ (R5 ∙ (R6 ∙ (R7 ∙ (R8 ∙ tail))))

  step4 : REST ∙ tail ≡ R2 ∙ (R3 ∙ (a1 ∙ Mtail))
  step4 =
      ∙-assoc R2 (R3 ∙ (R4 ∙ (R5 ∙ (R6 ∙ (R7 ∙ R8))))) tail
    ∙ cong (R2 ∙_)
        ( ∙-assoc R3 (R4 ∙ (R5 ∙ (R6 ∙ (R7 ∙ R8)))) tail
        ∙ cong (R3 ∙_)
            ( ∙-assoc R4 (R5 ∙ (R6 ∙ (R7 ∙ R8))) tail
            ∙ cong (R4 ∙_)
                ( ∙-assoc R5 (R6 ∙ (R7 ∙ R8)) tail
                ∙ cong (R5 ∙_)
                    ( ∙-assoc R6 (R7 ∙ R8) tail
                    ∙ cong (R6 ∙_) (∙-assoc R7 R8 tail)))
            ∙ cong (_∙ (R5 ∙ (R6 ∙ (R7 ∙ (R8 ∙ tail)))))
                   (cong-∙ Mu (∙-assoc c2 pQ cE) κ)
            ∙ ∙-assoc a1 cuκ (R5 ∙ (R6 ∙ (R7 ∙ (R8 ∙ tail)))) ))

  -- Step 5: the substComposite prefix collapses (associativity coherence).
  E-assoc : a1 ∙ (SCa ∙ SCb') ≡ sym (R2 ∙ R3)
  E-assoc =
      substComposite-assoc P c2 pQ cE u
    ∙ sym (symDistr R2 R3)

  prefix-refl : SCa ∙ (SCb' ∙ (R2 ∙ (R3 ∙ a1))) ≡ refl
  prefix-refl =
      sym (∙-assoc SCa SCb' (R2 ∙ (R3 ∙ a1)))
    ∙ cong ((SCa ∙ SCb') ∙_) (sym (∙-assoc R2 R3 a1))
    ∙ cancel-triangle a1 (SCa ∙ SCb') (R2 ∙ R3) E-assoc

  step5 : SCa ∙ (SCb' ∙ (R2 ∙ (R3 ∙ (a1 ∙ Mtail)))) ≡ Mtail
  step5 =
      cong (λ w → SCa ∙ (SCb' ∙ (R2 ∙ w))) (sym (∙-assoc R3 a1 Mtail))
    ∙ cong (λ w → SCa ∙ (SCb' ∙ w)) (sym (∙-assoc R2 (R3 ∙ a1) Mtail))
    ∙ cong (SCa ∙_) (sym (∙-assoc SCb' (R2 ∙ (R3 ∙ a1)) Mtail))
    ∙ sym (∙-assoc SCa (SCb' ∙ (R2 ∙ (R3 ∙ a1))) Mtail)
    ∙ cong (_∙ Mtail) prefix-refl
    ∙ sym (lUnit Mtail)

  -- Step 6: the right-hand chain is the tail of rew-cohLayer33.
  step6 : R8 ∙ tail ≡ cong (subst P pR) AG ∙ sym kM'
  step6 =
      sym (∙-assoc (cong (subst P pR) scsG)
                   (cong (subst P pR) (sym YG)) (sym kM'))
    ∙ cong (_∙ sym kM')
           (sym (cong-∙ (subst P pR) scsG (sym YG)))
    ∙ cong (λ w → cong (subst P pR) w ∙ sym kM')
           (sym (sigT-map-eq-decomp {S = S3} {Q = P} {f = rr} G e5 (sym kG)))

  MAIN : Lchain ≡ cuκ ∙ Rchain
  MAIN =
      cong (λ w → SCa ∙ (cong (subst P (pQ ∙ cE)) AF ∙ (SCb ∙ w))) step1
    ∙ cong (SCa ∙_) step2
    ∙ cong (λ w → SCa ∙ (SCb' ∙ w)) step3
    ∙ cong (λ w → SCa ∙ (SCb' ∙ w)) step4
    ∙ step5
    ∙ cong (λ w → cuκ ∙ (R5 ∙ (R6 ∙ (R7 ∙ w)))) step6

  main : subst (λ π → subst P π u ≡ w4) κ Lchain ≡ Rchain
  main =
      substInPathL cuκ Lchain
    ∙ cong (sym cuκ ∙_) MAIN
    ∙ ∙-cancel-l cuκ Rchain



-- The GpdLemmas statement is the special case T1 = T2 = T3, S2 = S3.
rew-coh2Painting-restr0 :
  {TU : Set ℓ} {TL : Set ℓ'} {A0 : Set ℓ''}
  {P : TL → Set ℓ'''} {S : TU → Set ℓ'''}
  {rq rr r0 : TU → TL}
  (F : (m : TU) → S m → P (rq m))
  (G : (n : TU) → S n → P (rr n))
  {d1 d2 : TU} (E1 : d1 ≡ d2)
  {m1 m2 : TU} (e2 : m1 ≡ m2)
  {n1 n2 : TU} (e5 : n1 ≡ n2)
  (pQ : rq m2 ≡ r0 d1) (pR : rr n2 ≡ r0 d2)
  (KA : rq m1 ≡ rr n1)
  (a0 : A0) (AR : A0 → S m1) (AQ1 : A0 → S n1)
  (HK : subst P KA (F m1 (AR a0)) ≡ G n1 (AQ1 a0))
  (κ : cong rq e2 ∙ (pQ ∙ cong r0 E1) ≡ KA ∙ (cong rr e5 ∙ pR))
  (u1 : S m2) (kF : u1 ≡ subst S e2 (AR a0))
  (u12 : S n2) (kG : u12 ≡ subst S e5 (AQ1 a0))
  (w3 : P (r0 d1)) (kM : w3 ≡ subst P pQ (F m2 u1))
  (w4 : P (r0 d2)) (kM' : w4 ≡ subst P pR (G n2 u12))
  → rew-coh2Painting-restr0-Type {P = P} {S = S}
      {rq = rq} {rr = rr} {r0 = r0}
      F G E1 e2 e5 pQ pR KA a0 AR AQ1 HK κ
      u1 kF u12 kG w3 kM w4 kM'
rew-coh2Painting-restr0 {P = P} {S = S} {rq = rq} {rr = rr} {r0 = r0}
  F G E1 e2 e5 pQ pR KA a0 AR AQ1 HK κ u1 kF u12 kG w3 kM w4 kM' =
  rew-coh2Painting-restr0-gen {P = P} {S2 = S} {S3 = S}
    {rq = rq} {rr = rr} {r0 = r0}
    F G E1 e2 e5 pQ pR KA a0 AR AQ1 HK κ u1 kF u12 kG w3 kM w4 kM'
-- Right cancellation as an inference rule.
∙-cancel-rᵉ : {x y z : A} {X Y : x ≡ y} (s : y ≡ z) → X ∙ s ≡ Y ∙ s → X ≡ Y
∙-cancel-rᵉ {X = X} {Y = Y} s E =
  sym (∙-cancel-r X s) ∙ cong (_∙ sym s) E ∙ ∙-cancel-r Y s








------------------------------------------------------------------------
-- (i) The flat ⊙-calculus.
--
-- Sq P H q q' is the flat form of `subst (λ π → subst P π u ≡ w) H q ≡ q'`
-- (substInPathL has been applied once and for all): a fiber square whose
-- two sides are q and q', sitting over the base 2-cell H.
------------------------------------------------------------------------

Sq : {X : Set ℓ} (P : X → Set ℓ') {x z : X} {u : P x} {w : P z}
     {p p' : x ≡ z} (H : p ≡ p')
     (q : subst P p u ≡ w) (q' : subst P p' u ≡ w) → Set ℓ'
Sq P {u = u} H q q' = q ≡ cong (λ e → subst P e u) H ∙ q'

-- Back to the subst form the statements use.
Sq→subst : {X : Set ℓ} (P : X → Set ℓ') {x z : X} {u : P x} {w : P z}
           {p p' : x ≡ z} (H : p ≡ p')
           {q : subst P p u ≡ w} {q' : subst P p' u ≡ w}
           → Sq P H q q' → subst (λ π → subst P π u ≡ w) H q ≡ q'
Sq→subst P {u = u} H {q} {q'} s =
    substInPathL (cong (λ e → subst P e u) H) q
  ∙ cong (sym (cong (λ e → subst P e u) H) ∙_) s
  ∙ ∙-cancel-l (cong (λ e → subst P e u) H) q'

Sq-of-≡ : {X : Set ℓ} (P : X → Set ℓ') {x z : X} {u : P x} {w : P z}
          {p : x ≡ z} {q q' : subst P p u ≡ w}
          → q ≡ q' → Sq P (refl {x = p}) q q'
Sq-of-≡ P {q' = q'} e = e ∙ lUnit q'

-- Vertical composition of squares (the base cells compose with ∙).
Sq-∙ : {X : Set ℓ} (P : X → Set ℓ') {x z : X} {u : P x} {w : P z}
       {p p' p'' : x ≡ z} {H : p ≡ p'} {H' : p' ≡ p''}
       {q : subst P p u ≡ w} {q' : subst P p' u ≡ w} {q'' : subst P p'' u ≡ w}
       → Sq P H q q' → Sq P H' q' q'' → Sq P (H ∙ H') q q''
Sq-∙ P {u = u} {H = H} {H' = H'} {q'' = q''} s s' =
    s
  ∙ cong (cong (λ e → subst P e u) H ∙_) s'
  ∙ sym (∙-assoc (cong (λ e → subst P e u) H)
                 (cong (λ e → subst P e u) H') q'')
  ∙ cong (_∙ q'') (sym (cong-∙ (λ e → subst P e u) H H'))

Sq-sym : {X : Set ℓ} (P : X → Set ℓ') {x z : X} {u : P x} {w : P z}
         {p p' : x ≡ z} {H : p ≡ p'}
         {q : subst P p u ≡ w} {q' : subst P p' u ≡ w}
         → Sq P H q q' → Sq P (sym H) q' q
Sq-sym P {u = u} {H = H} {q = q} {q' = q'} s =
    sym (∙-cancel-l (cong (λ e → subst P e u) H) q')
  ∙ cong (sym (cong (λ e → subst P e u) H) ∙_) (sym s)

-- Re-index a square along an equality of base cells (the "corrective
-- cell" slot; the assembly below never needs it except at one named
-- place).
Sq-cast : {X : Set ℓ} (P : X → Set ℓ') {x z : X} {u : P x} {w : P z}
          {p p' : x ≡ z} {H H' : p ≡ p'}
          {q : subst P p u ≡ w} {q' : subst P p' u ≡ w}
          → H ≡ H' → Sq P H q q' → Sq P H' q q'
Sq-cast P {u = u} {q' = q'} e s =
  s ∙ cong (λ h → cong (λ e' → subst P e' u) h ∙ q') e


-- Left cancellation of ∙ as an inference rule.
∙-cancel-lᵉ : {x y z : A} (X : x ≡ y) {M N : y ≡ z} → X ∙ M ≡ X ∙ N → M ≡ N
∙-cancel-lᵉ X {M} {N} e =
  sym (∙-cancel-l X M) ∙ cong (sym X ∙_) e ∙ ∙-cancel-l X N

-- ⊙ is associative over ∙-assoc.
⊙-assoc-Sq :
  {X : Set ℓ} (P : X → Set ℓ') {x y y' z : X}
  {u : P x} {v : P y} {w : P y'} {t : P z}
  {p : x ≡ y} (q : subst P p u ≡ v)
  {p' : y ≡ y'} (q' : subst P p' v ≡ w)
  {p'' : y' ≡ z} (q'' : subst P p'' w ≡ t)
  → Sq P (∙-assoc p p' p'')
       (_⊙_ {P = P} (_⊙_ {P = P} q q') q'')
       (_⊙_ {P = P} q (_⊙_ {P = P} q' q''))
⊙-assoc-Sq P {u = u} {v = v} {w = w} {t = t} {p = p} q {p' = p'} q'
            {p'' = p''} q'' =
    cong (SCa ∙_)
      ( cong (_∙ q'')
          ( cong-∙ T'' SC1 (cong T' q ∙ q')
          ∙ cong (cong T'' SC1 ∙_) (cong-∙ T'' (cong T' q) q') )
      ∙ ∙-assoc XX (YY ∙ ZZ) q''
      ∙ cong (XX ∙_) (∙-assoc YY ZZ q'') )
  ∙ sym
      ( cong (cong Mu AA ∙_)
          ( cong (SCb ∙_)
              ( sym (∙-assoc (cong T2 q) SC2v MM)
              ∙ cong (_∙ MM) (hnat {f = T2} {g = T21}
                                   (λ zz → substComposite P p' p'' zz) q)
              ∙ ∙-assoc SC2u YY MM )
          ∙ sym (∙-assoc SCb SC2u (YY ∙ MM)) )
      ∙ sym (∙-assoc (cong Mu AA) (SCb ∙ SC2u) (YY ∙ MM))
      ∙ cong (_∙ (YY ∙ MM)) (substComposite-assoc P p p' p'' u)
      ∙ ∙-assoc SCa XX (YY ∙ MM) )
  where
  Mu : _ → _
  Mu e = subst P e u

  T' : _
  T' = subst P p'

  T'' : _
  T'' = subst P p''

  T2 : _
  T2 = subst P (p' ∙ p'')

  T21 : _ → _
  T21 zz = subst P p'' (subst P p' zz)

  AA : (p ∙ p') ∙ p'' ≡ p ∙ (p' ∙ p'')
  AA = ∙-assoc p p' p''

  SCa : subst P ((p ∙ p') ∙ p'') u ≡ subst P p'' (subst P (p ∙ p') u)
  SCa = substComposite P (p ∙ p') p'' u

  SC1 : subst P (p ∙ p') u ≡ subst P p' (subst P p u)
  SC1 = substComposite P p p' u

  SCb : subst P (p ∙ (p' ∙ p'')) u ≡ subst P (p' ∙ p'') (subst P p u)
  SCb = substComposite P p (p' ∙ p'') u

  SC2v : subst P (p' ∙ p'') v ≡ subst P p'' (subst P p' v)
  SC2v = substComposite P p' p'' v

  SC2u : subst P (p' ∙ p'') (subst P p u) ≡ T21 (subst P p u)
  SC2u = substComposite P p' p'' (subst P p u)

  XX : subst P p'' (subst P (p ∙ p') u) ≡ subst P p'' (subst P p' (subst P p u))
  XX = cong T'' SC1

  YY : T21 (subst P p u) ≡ T21 v
  YY = cong T21 q

  ZZ : subst P p'' (subst P p' v) ≡ subst P p'' w
  ZZ = cong T'' q'

  MM : subst P p'' (subst P p' v) ≡ t
  MM = ZZ ∙ q''

-- Whiskering a square by a ⊙-factor on the right.
⊙-whisker-l :
  {X : Set ℓ} (P : X → Set ℓ') {x y z : X} {u : P x} {v : P y} {w : P z}
  {p₁ p₂ : x ≡ y} {H : p₁ ≡ p₂}
  {q₁ : subst P p₁ u ≡ v} {q₂ : subst P p₂ u ≡ v}
  {p' : y ≡ z} (r : subst P p' v ≡ w)
  → Sq P H q₁ q₂
  → Sq P (cong (_∙ p') H) (_⊙_ {P = P} q₁ r) (_⊙_ {P = P} q₂ r)
⊙-whisker-l P {u = u} {p₁ = p₁} {p₂ = p₂} {H = H} {q₁ = q₁} {q₂ = q₂}
            {p' = p'} r s =
    cong (λ m → SC₁ ∙ (cong T' m ∙ r)) s
  ∙ cong (λ m → SC₁ ∙ (m ∙ r)) (cong-∙ T' MuH q₂)
  ∙ cong (SC₁ ∙_) (∙-assoc (cong T' MuH) (cong T' q₂) r)
  ∙ sym (∙-assoc SC₁ (cong T' MuH) (cong T' q₂ ∙ r))
  ∙ cong (_∙ (cong T' q₂ ∙ r))
         (sym (hnat {f = λ e → subst P (e ∙ p') u}
                    {g = λ e → subst P p' (subst P e u)}
                    (λ e → substComposite P e p' u) H))
  ∙ ∙-assoc (cong (λ e → subst P (e ∙ p') u) H) SC₂ (cong T' q₂ ∙ r)
  where
  MuH : subst P p₁ u ≡ subst P p₂ u
  MuH = cong (λ e → subst P e u) H

  T' : _
  T' = subst P p'

  SC₁ : subst P (p₁ ∙ p') u ≡ subst P p' (subst P p₁ u)
  SC₁ = substComposite P p₁ p' u

  SC₂ : subst P (p₂ ∙ p') u ≡ subst P p' (subst P p₂ u)
  SC₂ = substComposite P p₂ p' u

-- Whiskering a square by a ⊙-factor on the left; the core chain is
-- shared with the cancellation below.
⊙-whisker-r-core :
  {X : Set ℓ} (P : X → Set ℓ') {x y z : X} {u : P x} {v : P y} {w : P z}
  {p : x ≡ y} (r : subst P p u ≡ v)
  {p₁ p₂ : y ≡ z} (H : p₁ ≡ p₂) (q₂ : subst P p₂ v ≡ w)
  → substComposite P p p₁ u
    ∙ (cong (subst P p₁) r ∙ (cong (λ e → subst P e v) H ∙ q₂))
    ≡ cong (λ e → subst P e u) (cong (p ∙_) H)
      ∙ _⊙_ {P = P} r q₂
⊙-whisker-r-core P {u = u} {v = v} {p = p} r {p₁ = p₁} {p₂ = p₂} H q₂ =
    cong (SC₁ ∙_) (sym (∙-assoc (cong T₁ r) MvH q₂))
  ∙ cong (λ m → SC₁ ∙ (m ∙ q₂))
         (hnat {f = T₁} {g = T₂} (λ zz → cong (λ e → subst P e zz) H) r)
  ∙ cong (SC₁ ∙_) (∙-assoc NN (cong T₂ r) q₂)
  ∙ sym (∙-assoc SC₁ NN (cong T₂ r ∙ q₂))
  ∙ cong (_∙ (cong T₂ r ∙ q₂))
         (sym (hnat {f = λ e → subst P (p ∙ e) u}
                    {g = λ e → subst P e (subst P p u)}
                    (λ e → substComposite P p e u) H))
  ∙ ∙-assoc (cong (λ e → subst P (p ∙ e) u) H) SC₂ (cong T₂ r ∙ q₂)
  where
  T₁ : _
  T₁ = subst P p₁

  T₂ : _
  T₂ = subst P p₂

  MvH : subst P p₁ v ≡ subst P p₂ v
  MvH = cong (λ e → subst P e v) H

  NN : subst P p₁ (subst P p u) ≡ subst P p₂ (subst P p u)
  NN = cong (λ e → subst P e (subst P p u)) H

  SC₁ : subst P (p ∙ p₁) u ≡ subst P p₁ (subst P p u)
  SC₁ = substComposite P p p₁ u

  SC₂ : subst P (p ∙ p₂) u ≡ subst P p₂ (subst P p u)
  SC₂ = substComposite P p p₂ u

⊙-whisker-r :
  {X : Set ℓ} (P : X → Set ℓ') {x y z : X} {u : P x} {v : P y} {w : P z}
  {p : x ≡ y} (r : subst P p u ≡ v)
  {p₁ p₂ : y ≡ z} {H : p₁ ≡ p₂}
  {q₁ : subst P p₁ v ≡ w} {q₂ : subst P p₂ v ≡ w}
  → Sq P H q₁ q₂
  → Sq P (cong (p ∙_) H) (_⊙_ {P = P} r q₁) (_⊙_ {P = P} r q₂)
⊙-whisker-r P {p = p} r {H = H} {q₁ = q₁} {q₂ = q₂} s =
    cong (λ m → substComposite P p _ _ ∙ (cong (subst P _) r ∙ m)) s
  ∙ ⊙-whisker-r-core P r H q₂

-- … and its converse: a leading ⊙-factor cancels.
⊙-cancel-r :
  {X : Set ℓ} (P : X → Set ℓ') {x y z : X} {u : P x} {v : P y} {w : P z}
  {p : x ≡ y} (r : subst P p u ≡ v)
  {p₁ p₂ : y ≡ z} {H : p₁ ≡ p₂}
  {q₁ : subst P p₁ v ≡ w} {q₂ : subst P p₂ v ≡ w}
  → Sq P (cong (p ∙_) H) (_⊙_ {P = P} r q₁) (_⊙_ {P = P} r q₂)
  → Sq P H q₁ q₂
⊙-cancel-r P {p = p} r {p₁ = p₁} {H = H} {q₁ = q₁} {q₂ = q₂} s =
  ∙-cancel-lᵉ (cong (subst P p₁) r)
    (∙-cancel-lᵉ (substComposite P p p₁ _)
      (s ∙ sym (⊙-whisker-r-core P r H q₂)))


------------------------------------------------------------------------
-- (v.a) The fiber zig3: the pasting of three fiber squares, mirroring
-- the base-level zig3 STEP FOR STEP, so that the base cell it produces
-- is literally `zig3 α β γ δ Kx Ky Kz E1 E2 E3 A1 A2 A3`.
------------------------------------------------------------------------

zig3-Sq :
  {X : Set ℓ} (P : X → Set ℓ')
  {a₀ a₁ a₂ a₃ r₀ r₁ r₂ r₃ : X}
  {α : a₀ ≡ r₀} {β : a₁ ≡ r₁} {γ : a₂ ≡ r₂} {δ : a₃ ≡ r₃}
  {Kx : a₀ ≡ a₁} {Ky : a₁ ≡ a₂} {Kz : a₂ ≡ a₃}
  {E1 : r₀ ≡ r₁} {E2 : r₁ ≡ r₂} {E3 : r₂ ≡ r₃}
  {A1 : α ∙ E1 ≡ Kx ∙ β} {A2 : β ∙ E2 ≡ Ky ∙ γ} {A3 : γ ∙ E3 ≡ Kz ∙ δ}
  {n₀ : P a₀} {n₁ : P a₁} {n₂ : P a₂} {n₃ : P a₃}
  {m₀ : P r₀} {m₁ : P r₁} {m₂ : P r₂} {m₃ : P r₃}
  (α̃ : subst P α n₀ ≡ m₀) (β̃ : subst P β n₁ ≡ m₁)
  (γ̃ : subst P γ n₂ ≡ m₂) (δ̃ : subst P δ n₃ ≡ m₃)
  (K̃x : subst P Kx n₀ ≡ n₁) (K̃y : subst P Ky n₁ ≡ n₂)
  (K̃z : subst P Kz n₂ ≡ n₃)
  (Ẽ1 : subst P E1 m₀ ≡ m₁) (Ẽ2 : subst P E2 m₁ ≡ m₂)
  (Ẽ3 : subst P E3 m₂ ≡ m₃)
  (Ã1 : Sq P A1 (_⊙_ {P = P} α̃ Ẽ1) (_⊙_ {P = P} K̃x β̃))
  (Ã2 : Sq P A2 (_⊙_ {P = P} β̃ Ẽ2) (_⊙_ {P = P} K̃y γ̃))
  (Ã3 : Sq P A3 (_⊙_ {P = P} γ̃ Ẽ3) (_⊙_ {P = P} K̃z δ̃))
  → Sq P (zig3 α β γ δ Kx Ky Kz E1 E2 E3 A1 A2 A3)
       (_⊙_ {P = P} α̃ (_⊙_ {P = P} Ẽ1 (_⊙_ {P = P} Ẽ2 Ẽ3)))
       (_⊙_ {P = P} (_⊙_ {P = P} K̃x (_⊙_ {P = P} K̃y K̃z)) δ̃)
zig3-Sq P α̃ β̃ γ̃ δ̃ K̃x K̃y K̃z Ẽ1 Ẽ2 Ẽ3 Ã1 Ã2 Ã3 =
  Sq-∙ P (Sq-sym P (⊙-assoc-Sq P α̃ Ẽ1 (_⊙_ {P = P} Ẽ2 Ẽ3)))
    (Sq-∙ P (⊙-whisker-l P (_⊙_ {P = P} Ẽ2 Ẽ3) Ã1)
      (Sq-∙ P (⊙-assoc-Sq P K̃x β̃ (_⊙_ {P = P} Ẽ2 Ẽ3))
        (Sq-∙ P (⊙-whisker-r P K̃x inner)
                (Sq-sym P (⊙-assoc-Sq P K̃x (_⊙_ {P = P} K̃y K̃z) δ̃)))))
  where
  inner : Sq P _ (_⊙_ {P = P} β̃ (_⊙_ {P = P} Ẽ2 Ẽ3))
                 (_⊙_ {P = P} (_⊙_ {P = P} K̃y K̃z) δ̃)
  inner =
    Sq-∙ P (Sq-sym P (⊙-assoc-Sq P β̃ Ẽ2 Ẽ3))
      (Sq-∙ P (⊙-whisker-l P Ẽ3 Ã2)
        (Sq-∙ P (⊙-assoc-Sq P K̃y γ̃ Ẽ3)
          (Sq-∙ P (⊙-whisker-r P K̃y Ã3)
                  (Sq-sym P (⊙-assoc-Sq P K̃y K̃z δ̃)))))


------------------------------------------------------------------------
-- (ii) sigT-map-eq transports a fiber square along a map: the fiber
-- analogue of map-square's "push HH1 along rfq" step.  By
-- sigT-map-eq-decomp both sides are substCommSlice ∙ cong (g y) ⟨…⟩, so
-- this is cong-∙ distribution plus the naturality of substCommSlice in
-- its PATH argument (hnat on λ p → substCommSlice f g p u).
------------------------------------------------------------------------

sigT-map-eq-Sq :
  {A : Set ℓ} {B : Set ℓ'} {S : A → Set ℓ''} {Q : B → Set ℓ'''}
  {f : A → B} (g : (a : A) → S a → Q (f a))
  {x y : A} {u : S x} {v : S y} {p p' : x ≡ y} {H : p ≡ p'}
  {q : subst S p u ≡ v} {q' : subst S p' u ≡ v}
  → Sq S H q q'
  → Sq Q (cong (cong f) H)
       (sigT-map-eq {P = S} {Q = Q} {f = f} g {p = p} q)
       (sigT-map-eq {P = S} {Q = Q} {f = f} g {p = p'} q')
sigT-map-eq-Sq {S = S} {Q = Q} {f = f} g {y = y} {u = u} {p = p} {p' = p'}
               {H = H} {q = q} {q' = q'} s =
    sigT-map-eq-decomp {S = S} {Q = Q} {f = f} g p q
  ∙ cong (scs p ∙_) (cong (cong (g y)) s ∙ cong-∙ (g y) MuH q')
  ∙ sym (∙-assoc (scs p) (cong (g y) MuH) (cong (g y) q'))
  ∙ cong (_∙ cong (g y) q')
         (sym (hnat {f = λ e → subst Q (cong f e) (g _ u)}
                    {g = λ e → g y (subst S e u)}
                    (λ e → substCommSlice {S = S} {P = Q} f g e u) H))
  ∙ ∙-assoc (cong (λ e → subst Q (cong f e) (g _ u)) H) (scs p')
            (cong (g y) q')
  ∙ cong (cong (λ e → subst Q (cong f e) (g _ u)) H ∙_)
         (sym (sigT-map-eq-decomp {S = S} {Q = Q} {f = f} g p' q'))
  where
  scs : (r : _ ≡ y) → _
  scs r = substCommSlice {S = S} {P = Q} f g r u

  MuH : subst S p u ≡ subst S p' u
  MuH = cong (λ e → subst S e u) H


------------------------------------------------------------------------
-- substCommSlice is compatible with composition of base paths: the
-- keystone of the ⊙-image lemma below.
------------------------------------------------------------------------

scs-comp-base :
  {A : Set ℓ} {B : Set ℓ'} {S : A → Set ℓ''} {Q : B → Set ℓ'''}
  {f : A → B} (g : (a : A) → S a → Q (f a))
  {x y : A} (p : x ≡ y) (u : S x)
  → substCommSlice {S = S} {P = Q} f g (p ∙ refl) u
    ∙ cong (g y) (substComposite S p refl u)
    ≡ cong (λ e → subst Q e (g x u)) (cong-∙ f p refl)
      ∙ ( substComposite Q (cong f p) refl (g x u)
        ∙ ( cong (subst Q refl) (substCommSlice {S = S} {P = Q} f g p u)
          ∙ substCommSlice {S = S} {P = Q} f g refl (subst S p u) ) )
scs-comp-base {S = S} {Q = Q} {f = f} g {x = x} {y = y} p u =
    cong (scsPR ∙_)
      ( cong (cong (g y)) (substComposite-refl S p u)
      ∙ cong-∙ (g y) (cong (λ e → subst S e u) (sym (rUnit p))) (sym tSv) )
  ∙ cong (_∙ (sym V ∙ W)) fEq
  ∙ ∙-assoc (sym U) (scsP ∙ V) (sym V ∙ W)
  ∙ cong (sym U ∙_) ( ∙-assoc scsP V (sym V ∙ W)
                    ∙ cong (scsP ∙_) (∙-cancel-l (sym V) W) )
  ∙ sym RHSeq
  where
  v : S y
  v = subst S p u

  tSv : subst S refl v ≡ v
  tSv = substRefl S v

  scsP : subst Q (cong f p) (g x u) ≡ g y v
  scsP = substCommSlice {S = S} {P = Q} f g p u

  scsPR : subst Q (cong f (p ∙ refl)) (g x u) ≡ g y (subst S (p ∙ refl) u)
  scsPR = substCommSlice {S = S} {P = Q} f g (p ∙ refl) u

  U : subst Q (cong f p) (g x u) ≡ subst Q (cong f (p ∙ refl)) (g x u)
  U = cong (λ e → subst Q (cong f e) (g x u)) (rUnit p)

  V : g y v ≡ g y (subst S (p ∙ refl) u)
  V = cong (λ e → g y (subst S e u)) (rUnit p)

  W : g y v ≡ g y (subst S refl v)
  W = cong (g y) (sym tSv)

  AQ : Q (f y)
  AQ = subst Q (cong f p) (g x u)

  BQ : Q (f y)
  BQ = g y v

  tQA : subst Q refl AQ ≡ AQ
  tQA = substRefl Q AQ

  tQB : subst Q refl BQ ≡ BQ
  tQB = substRefl Q BQ

  R : AQ ≡ subst Q (cong f p ∙ refl) (g x u)
  R = cong (λ e → subst Q e (g x u)) (rUnit (cong f p))

  fEq : scsPR ≡ sym U ∙ (scsP ∙ V)
  fEq =
      sym (∙-cancel-l U scsPR)
    ∙ cong (sym U ∙_)
           (hnat {f = λ e → subst Q (cong f e) (g x u)}
                 {g = λ e → g y (subst S e u)}
                 (λ e → substCommSlice {S = S} {P = Q} f g e u) (rUnit p))

  innerEq : cong (subst Q refl) scsP
            ∙ substCommSlice {S = S} {P = Q} f g refl v
            ≡ tQA ∙ (scsP ∙ W)
  innerEq =
      cong (_∙ substCommSlice {S = S} {P = Q} f g refl v)
           (substRefl-natural {P = Q} scsP)
    ∙ cong ((tQA ∙ (scsP ∙ sym tQB)) ∙_)
           (substCommSlice-refl {S = S} {Q = Q} f g v)
    ∙ ∙-assoc tQA (scsP ∙ sym tQB) (tQB ∙ W)
    ∙ cong (tQA ∙_) ( ∙-assoc scsP (sym tQB) (tQB ∙ W)
                    ∙ cong (scsP ∙_) (∙-cancel-l tQB W) )

  RHSeq : cong (λ e → subst Q e (g x u)) (cong-∙ f p refl)
          ∙ ( substComposite Q (cong f p) refl (g x u)
            ∙ (cong (subst Q refl) scsP
               ∙ substCommSlice {S = S} {P = Q} f g refl v) )
          ≡ sym U ∙ (scsP ∙ W)
  RHSeq =
      cong (λ zz → zz ∙ (substComposite Q (cong f p) refl (g x u)
                         ∙ (cong (subst Q refl) scsP
                            ∙ substCommSlice {S = S} {P = Q} f g refl v)))
           ( cong (cong (λ e → subst Q e (g x u))) (cong-∙-refl f p)
           ∙ cong-∙ (λ e → subst Q e (g x u))
                    (cong (cong f) (sym (rUnit p))) (rUnit (cong f p)) )
    ∙ cong (λ zz → (sym U ∙ R) ∙ (zz ∙ (cong (subst Q refl) scsP
                                        ∙ substCommSlice {S = S} {P = Q}
                                                         f g refl v)))
           (substComposite-refl Q (cong f p) (g x u))
    ∙ cong (λ zz → (sym U ∙ R) ∙ ((sym R ∙ sym tQA) ∙ zz)) innerEq
    ∙ cong ((sym U ∙ R) ∙_)
           ( ∙-assoc (sym R) (sym tQA) (tQA ∙ (scsP ∙ W))
           ∙ cong (sym R ∙_) (∙-cancel-l tQA (scsP ∙ W)) )
    ∙ ∙-assoc (sym U) R (sym R ∙ (scsP ∙ W))
    ∙ cong (sym U ∙_) (∙-cancel-l (sym R) (scsP ∙ W))

scs-comp :
  {A : Set ℓ} {B : Set ℓ'} {S : A → Set ℓ''} {Q : B → Set ℓ'''}
  {f : A → B} (g : (a : A) → S a → Q (f a))
  {x y z : A} (p : x ≡ y) (p' : y ≡ z) (u : S x)
  → substCommSlice {S = S} {P = Q} f g (p ∙ p') u
    ∙ cong (g z) (substComposite S p p' u)
    ≡ cong (λ e → subst Q e (g x u)) (cong-∙ f p p')
      ∙ ( substComposite Q (cong f p) (cong f p') (g x u)
        ∙ ( cong (subst Q (cong f p')) (substCommSlice {S = S} {P = Q} f g p u)
          ∙ substCommSlice {S = S} {P = Q} f g p' (subst S p u) ) )
scs-comp {S = S} {Q = Q} {f = f} g p p' u =
  J (λ z p' → substCommSlice {S = S} {P = Q} f g (p ∙ p') u
              ∙ cong (g z) (substComposite S p p' u)
              ≡ cong (λ e → subst Q e (g _ u)) (cong-∙ f p p')
                ∙ ( substComposite Q (cong f p) (cong f p') (g _ u)
                  ∙ ( cong (subst Q (cong f p'))
                           (substCommSlice {S = S} {P = Q} f g p u)
                    ∙ substCommSlice {S = S} {P = Q} f g p' (subst S p u) ) ))
    (scs-comp-base {S = S} {Q = Q} {f = f} g p u)
    p'


-- sigT-map-eq distributes over ⊙, over the base cell cong-∙.
sigT-map-eq-⊙ :
  {A : Set ℓ} {B : Set ℓ'} {S : A → Set ℓ''} {Q : B → Set ℓ'''}
  {f : A → B} (g : (a : A) → S a → Q (f a))
  {x y z : A} {u : S x} {v : S y} {w : S z}
  {p : x ≡ y} (q : subst S p u ≡ v)
  {p' : y ≡ z} (q' : subst S p' v ≡ w)
  → Sq Q (cong-∙ f p p')
       (sigT-map-eq {P = S} {Q = Q} {f = f} g {p = p ∙ p'}
                    (_⊙_ {P = S} q q'))
       (_⊙_ {P = Q} (sigT-map-eq {P = S} {Q = Q} {f = f} g {p = p} q)
                    (sigT-map-eq {P = S} {Q = Q} {f = f} g {p = p'} q'))
sigT-map-eq-⊙ {S = S} {Q = Q} {f = f} g {x = x} {y = y} {z = z} {u = u}
              {p = p} q {p' = p'} q' =
    sigT-map-eq-decomp {S = S} {Q = Q} {f = f} g (p ∙ p') (_⊙_ {P = S} q q')
  ∙ cong (scsPP ∙_)
      ( cong-∙ (g z) SCS (cong T' q ∙ q')
      ∙ cong (cong (g z) SCS ∙_) (cong-∙ (g z) (cong T' q) q') )
  ∙ sym (∙-assoc scsPP (cong (g z) SCS) (CQ ∙ Cq'))
  ∙ cong (_∙ (CQ ∙ Cq')) (scs-comp {S = S} {Q = Q} {f = f} g p p' u)
  ∙ ∙-assoc (cong MQ cc) (SCQ ∙ (XX ∙ YY)) (CQ ∙ Cq')
  ∙ cong (cong MQ cc ∙_) inner
  ∙ cong (cong MQ cc ∙_) (sym rhs)
  where
  MQ : _ → _
  MQ e = subst Q e (g x u)

  cc : cong f (p ∙ p') ≡ cong f p ∙ cong f p'
  cc = cong-∙ f p p'

  T' : _
  T' = subst S p'

  TQ' : _
  TQ' = subst Q (cong f p')

  SCS : subst S (p ∙ p') u ≡ subst S p' (subst S p u)
  SCS = substComposite S p p' u

  SCQ : subst Q (cong f p ∙ cong f p') (g x u)
        ≡ subst Q (cong f p') (subst Q (cong f p) (g x u))
  SCQ = substComposite Q (cong f p) (cong f p') (g x u)

  scsPP : subst Q (cong f (p ∙ p')) (g x u) ≡ g z (subst S (p ∙ p') u)
  scsPP = substCommSlice {S = S} {P = Q} f g (p ∙ p') u

  scsP : subst Q (cong f p) (g x u) ≡ g y (subst S p u)
  scsP = substCommSlice {S = S} {P = Q} f g p u

  scsP'u : subst Q (cong f p') (g y (subst S p u)) ≡ g z (subst S p' (subst S p u))
  scsP'u = substCommSlice {S = S} {P = Q} f g p' (subst S p u)

  scsP'v : subst Q (cong f p') (g y _) ≡ g z (subst S p' _)
  scsP'v = substCommSlice {S = S} {P = Q} f g p' _

  XX : subst Q (cong f p') (subst Q (cong f p) (g x u))
       ≡ subst Q (cong f p') (g y (subst S p u))
  XX = cong TQ' scsP

  YY : _
  YY = scsP'u

  CQ : g z (subst S p' (subst S p u)) ≡ g z (subst S p' _)
  CQ = cong (λ s → g z (subst S p' s)) q

  Cq' : _
  Cq' = cong (g z) q'

  XX' : subst Q (cong f p') (g y (subst S p u)) ≡ subst Q (cong f p') (g y _)
  XX' = cong (λ s → subst Q (cong f p') (g y s)) q

  inner : (SCQ ∙ (XX ∙ YY)) ∙ (CQ ∙ Cq')
          ≡ SCQ ∙ ((XX ∙ XX') ∙ (scsP'v ∙ Cq'))
  inner =
      ∙-assoc SCQ (XX ∙ YY) (CQ ∙ Cq')
    ∙ cong (SCQ ∙_)
        ( ∙-assoc XX YY (CQ ∙ Cq')
        ∙ cong (XX ∙_)
            ( sym (∙-assoc YY CQ Cq')
            ∙ cong (_∙ Cq')
                   (sym (hnat {f = λ s → subst Q (cong f p') (g y s)}
                              {g = λ s → g z (subst S p' s)}
                              (λ s → substCommSlice {S = S} {P = Q} f g p' s)
                              q))
            ∙ ∙-assoc XX' scsP'v Cq' )
        ∙ sym (∙-assoc XX XX' (scsP'v ∙ Cq')) )

  rhs : _⊙_ {P = Q} (sigT-map-eq {P = S} {Q = Q} {f = f} g {p = p} q)
                    (sigT-map-eq {P = S} {Q = Q} {f = f} g {p = p'} q')
        ≡ SCQ ∙ ((XX ∙ XX') ∙ (scsP'v ∙ Cq'))
  rhs =
      cong (λ m → SCQ ∙ (cong TQ' m ∙ sigT-map-eq {P = S} {Q = Q} {f = f} g
                                                  {p = p'} q'))
           (sigT-map-eq-decomp {S = S} {Q = Q} {f = f} g p q)
    ∙ cong (λ m → SCQ ∙ (cong TQ' (scsP ∙ cong (g y) q) ∙ m))
           (sigT-map-eq-decomp {S = S} {Q = Q} {f = f} g p' q')
    ∙ cong (λ m → SCQ ∙ (m ∙ (scsP'v ∙ Cq')))
           (cong-∙ TQ' scsP (cong (g y) q))


------------------------------------------------------------------------
-- Prerequisites of (iv): transport in a path family with both ends
-- moving, and substComposite at a refl LEFT argument.
------------------------------------------------------------------------

substInPathLR : {W : Set ℓ} {T : Set ℓ'} (M N : W → T) {c c' : W}
                (e : c ≡ c') (q : M c ≡ N c)
                → subst (λ cc → M cc ≡ N cc) e q ≡ sym (cong M e) ∙ (q ∙ cong N e)
substInPathLR M N e q =
  J (λ _ e → subst (λ cc → M cc ≡ N cc) e q ≡ sym (cong M e) ∙ (q ∙ cong N e))
    (transportRefl q ∙ (rUnit q ∙ lUnit (q ∙ refl)))
    e

-- transportRefl is natural at its own argument (h (h x) coherence).
transportRefl-nat : {A : Set ℓ} (P : A → Set ℓ') {x : A} (u : P x)
  → cong (subst P refl) (substRefl P u) ≡ substRefl P (subst P refl u)
transportRefl-nat P u =
  ∙-cancel-rᵉ (substRefl P u)
    (hnat {f = subst P refl} {g = λ zz → zz} (substRefl P) (substRefl P u))

lUnit-refl : {x : A} → lUnit (refl {x = x}) ≡ rUnit (refl {x = x})
lUnit-refl {x = x} = JRefl (λ _ p → p ≡ refl ∙ p) (rUnit (refl {x = x}))

substComposite-lrefl : {A : Set ℓ} (P : A → Set ℓ') {x y : A}
  (q : x ≡ y) (u : P x)
  → substComposite P refl q u
    ≡ cong (λ e → subst P e u) (sym (lUnit q))
      ∙ cong (subst P q) (sym (substRefl P u))
substComposite-lrefl P q u =
  J (λ _ q → substComposite P refl q u
             ≡ cong (λ e → subst P e u) (sym (lUnit q))
               ∙ cong (subst P q) (sym (substRefl P u)))
    ( substComposite-refl P refl u
    ∙ cong (λ h → cong (λ e → subst P e u) (sym h)
                  ∙ sym (substRefl P (subst P refl u)))
           (sym lUnit-refl)
    ∙ cong (λ h → cong (λ e → subst P e u) (sym (lUnit refl)) ∙ sym h)
           (sym (transportRefl-nat P u)) )
    q


------------------------------------------------------------------------
-- (iv) The (z , c)-naturality of a family of subst-equations
-- (HKA2/HKA4/HKA6), over the naturality square of its base family.
------------------------------------------------------------------------

hnat-refl : {A : Set ℓ} {B : Set ℓ'} {f g : A → B}
            (H : (a : A) → f a ≡ g a) {a : A}
            → hnat H (refl {x = a}) ≡ sym (lUnit (H a)) ∙ rUnit (H a)
hnat-refl {f = f} {g = g} H {a} =
  JRefl (λ a' ρ → cong f ρ ∙ H a' ≡ H a ∙ cong g ρ)
        (sym (lUnit (H a)) ∙ rUnit (H a))

family-Sq-base :
  {X2 : Set ℓ} {X0 : Set ℓ'} {S2 : X2 → Set ℓ''} {S0 : X0 → Set ℓ'''}
  {fL fR : X2 → X0}
  (FL : (z : X2) → S2 z → S0 (fL z)) (FR : (z : X2) → S2 z → S0 (fR z))
  (KA : (z : X2) → fL z ≡ fR z)
  (HKA : (z : X2) (c : S2 z) → subst S0 (KA z) (FL z c) ≡ FR z c)
  (z1 : X2) (c1 : S2 z1)
  → Sq S0 (hnat KA (refl {x = z1}))
       (_⊙_ {P = S0}
            (sigT-map-eq {P = S2} {Q = S0} {f = fL} FL {p = refl}
                         (refl {x = subst S2 refl c1}))
            (HKA z1 (subst S2 refl c1)))
       (_⊙_ {P = S0} (HKA z1 c1)
            (sigT-map-eq {P = S2} {Q = S0} {f = fR} FR {p = refl}
                         (refl {x = subst S2 refl c1})))
family-Sq-base {S2 = S2} {S0 = S0} {fL = fL} {fR = fR} FL FR KA HKA z1 c1 =
  lhsEq ∙ sym rhsEq
  where
  K : _
  K = KA z1

  a : _
  a = FL z1 c1

  b : _
  b = FR z1 c1

  t : subst S2 refl c1 ≡ c1
  t = substRefl S2 c1

  tA : subst S0 refl a ≡ a
  tA = substRefl S0 a

  tB : subst S0 refl b ≡ b
  tB = substRefl S0 b

  tKA : subst S0 refl (subst S0 K a) ≡ subst S0 K a
  tKA = substRefl S0 (subst S0 K a)

  FLt : a ≡ FL z1 (subst S2 refl c1)
  FLt = cong (FL z1) (sym t)

  FRt : b ≡ FR z1 (subst S2 refl c1)
  FRt = cong (FR z1) (sym t)

  h : subst S0 K a ≡ b
  h = HKA z1 c1

  h' : subst S0 K (FL z1 (subst S2 refl c1)) ≡ FR z1 (subst S2 refl c1)
  h' = HKA z1 (subst S2 refl c1)

  cK : {u v : _} → u ≡ v → subst S0 K u ≡ subst S0 K v
  cK = cong (subst S0 K)

  ca : {e e' : _} → e ≡ e' → subst S0 e a ≡ subst S0 e' a
  ca = cong (λ e → subst S0 e a)

  mfL : subst S0 refl a ≡ FL z1 (subst S2 refl c1)
  mfL = sigT-map-eq {P = S2} {Q = S0} {f = fL} FL {p = refl}
                    (refl {x = subst S2 refl c1})

  mfR : subst S0 refl b ≡ FR z1 (subst S2 refl c1)
  mfR = sigT-map-eq {P = S2} {Q = S0} {f = fR} FR {p = refl}
                    (refl {x = subst S2 refl c1})

  mfLeq : mfL ≡ tA ∙ FLt
  mfLeq = sigT-map-eq-filler {S = S2} {Q = S0} {f = fL} FL refl c1
          ∙ substCommSlice-refl {S = S2} {Q = S0} fL FL c1

  mfReq : mfR ≡ tB ∙ FRt
  mfReq = sigT-map-eq-filler {S = S2} {Q = S0} {f = fR} FR refl c1
          ∙ substCommSlice-refl {S = S2} {Q = S0} fR FR c1

  cNat : h' ≡ sym (cK FLt) ∙ (h ∙ FRt)
  cNat =
      sym (fromPathP {P = λ i → subst S0 K (FL z1 (sym t i))
                                ≡ FR z1 (sym t i)}
                     (λ i → HKA z1 (sym t i)))
    ∙ substInPathLR (λ c → subst S0 K (FL z1 c)) (FR z1) (sym t) h

  lhsEq : _⊙_ {P = S0} mfL h' ≡ ca (sym (lUnit K)) ∙ (h ∙ FRt)
  lhsEq =
      cong (λ m → substComposite S0 refl K a ∙ (cK m ∙ h')) mfLeq
    ∙ cong (λ m → substComposite S0 refl K a ∙ (m ∙ h'))
           (cong-∙ (subst S0 K) tA FLt)
    ∙ cong (λ m → substComposite S0 refl K a ∙ ((cK tA ∙ cK FLt) ∙ m)) cNat
    ∙ cong (substComposite S0 refl K a ∙_)
           ( ∙-assoc (cK tA) (cK FLt) (sym (cK FLt) ∙ (h ∙ FRt))
           ∙ cong (cK tA ∙_) (∙-cancel-l (sym (cK FLt)) (h ∙ FRt)) )
    ∙ cong (_∙ (cK tA ∙ (h ∙ FRt))) (substComposite-lrefl S0 K a)
    ∙ ∙-assoc (ca (sym (lUnit K))) (cK (sym tA)) (cK tA ∙ (h ∙ FRt))
    ∙ cong (ca (sym (lUnit K)) ∙_) (∙-cancel-l (cK tA) (h ∙ FRt))

  rhsEq : ca (hnat KA (refl {x = z1})) ∙ _⊙_ {P = S0} h mfR
          ≡ ca (sym (lUnit K)) ∙ (h ∙ FRt)
  rhsEq =
      cong (λ m → ca m ∙ _⊙_ {P = S0} h mfR) (hnat-refl KA)
    ∙ cong (_∙ _⊙_ {P = S0} h mfR)
           (cong-∙ (λ e → subst S0 e a) (sym (lUnit K)) (rUnit K))
    ∙ cong (λ m → (ca (sym (lUnit K)) ∙ ca (rUnit K))
                  ∙ (m ∙ (cong (subst S0 refl) h ∙ mfR)))
           (substComposite-refl S0 K a)
    ∙ cong (λ m → (ca (sym (lUnit K)) ∙ ca (rUnit K))
                  ∙ ((ca (sym (rUnit K)) ∙ sym tKA) ∙ (m ∙ mfR)))
           (substRefl-natural {P = S0} h)
    ∙ cong (λ m → (ca (sym (lUnit K)) ∙ ca (rUnit K))
                  ∙ ((ca (sym (rUnit K)) ∙ sym tKA)
                     ∙ ((tKA ∙ (h ∙ sym tB)) ∙ m)))
           mfReq
    ∙ cong (λ m → (ca (sym (lUnit K)) ∙ ca (rUnit K))
                  ∙ ((ca (sym (rUnit K)) ∙ sym tKA) ∙ m))
           ( ∙-assoc tKA (h ∙ sym tB) (tB ∙ FRt)
           ∙ cong (tKA ∙_) ( ∙-assoc h (sym tB) (tB ∙ FRt)
                           ∙ cong (h ∙_) (∙-cancel-l tB FRt) ) )
    ∙ cong ((ca (sym (lUnit K)) ∙ ca (rUnit K)) ∙_)
           ( ∙-assoc (ca (sym (rUnit K))) (sym tKA) (tKA ∙ (h ∙ FRt))
           ∙ cong (ca (sym (rUnit K)) ∙_) (∙-cancel-l tKA (h ∙ FRt)) )
    ∙ ∙-assoc (ca (sym (lUnit K))) (ca (rUnit K))
              (ca (sym (rUnit K)) ∙ (h ∙ FRt))
    ∙ cong (ca (sym (lUnit K)) ∙_)
           (∙-cancel-l (ca (sym (rUnit K))) (h ∙ FRt))

family-Sq :
  {X2 : Set ℓ} {X0 : Set ℓ'} {S2 : X2 → Set ℓ''} {S0 : X0 → Set ℓ'''}
  {fL fR : X2 → X0}
  (FL : (z : X2) → S2 z → S0 (fL z)) (FR : (z : X2) → S2 z → S0 (fR z))
  (KA : (z : X2) → fL z ≡ fR z)
  (HKA : (z : X2) (c : S2 z) → subst S0 (KA z) (FL z c) ≡ FR z c)
  {z1 z2 : X2} (pI : z1 ≡ z2) {c1 : S2 z1} {c2 : S2 z2}
  (k : subst S2 pI c1 ≡ c2)
  → Sq S0 (hnat KA pI)
       (_⊙_ {P = S0}
            (sigT-map-eq {P = S2} {Q = S0} {f = fL} FL {p = pI} k)
            (HKA z2 c2))
       (_⊙_ {P = S0} (HKA z1 c1)
            (sigT-map-eq {P = S2} {Q = S0} {f = fR} FR {p = pI} k))
family-Sq {S2 = S2} {S0 = S0} {fL = fL} {fR = fR} FL FR KA HKA
          {z1 = z1} pI {c1 = c1} k =
  J (λ z2 pI → {c2 : S2 z2} (k : subst S2 pI c1 ≡ c2)
               → Sq S0 (hnat KA pI)
                    (_⊙_ {P = S0}
                         (sigT-map-eq {P = S2} {Q = S0} {f = fL} FL {p = pI} k)
                         (HKA z2 c2))
                    (_⊙_ {P = S0} (HKA z1 c1)
                         (sigT-map-eq {P = S2} {Q = S0} {f = fR} FR
                                      {p = pI} k)))
    (λ {c2} k →
       J (λ c2 k → Sq S0 (hnat KA (refl {x = z1}))
                      (_⊙_ {P = S0}
                           (sigT-map-eq {P = S2} {Q = S0} {f = fL} FL
                                        {p = refl} k)
                           (HKA z1 c2))
                      (_⊙_ {P = S0} (HKA z1 c1)
                           (sigT-map-eq {P = S2} {Q = S0} {f = fR} FR
                                        {p = refl} k)))
         (family-Sq-base {S2 = S2} {S0 = S0} {fL = fL} {fR = fR}
                         FL FR KA HKA z1 c1)
         k)
    pI k


------------------------------------------------------------------------
-- (v.b) The g-conjugation bridge: Φ dd = subst S0 (g dd) ∘ F (uf0 dd)
-- maps a level-1 chain the same way F does, after conjugating by g.
------------------------------------------------------------------------

twist-core-base :
  {X1 : Set ℓ} {X0 : Set ℓ'} {TU : Set ℓ''} {T : Set ℓ'''}
  {S1 : X1 → Set ℓp} {S0 : X0 → Set ℓp}
  {uf0 : TU → X1} {rf0 : T → X0} {fX : TU → T} {rf : X1 → X0}
  (F : (y : X1) → S1 y → S0 (rf y))
  (g : (dd : TU) → rf (uf0 dd) ≡ rf0 (fX dd))
  (u0 : TU) (bP : S1 (uf0 u0))
  → substComposite S0 (g u0) refl (F (uf0 u0) bP)
    ∙ substCommSlice {S = λ dd → S1 (uf0 dd)} {P = λ dd → S0 (rf0 dd)}
        fX (λ dd x → subst S0 (g dd) (F (uf0 dd) x)) refl bP
    ≡ cong (λ e → subst S0 e (F (uf0 u0) bP)) (sym (hnat g (refl {x = u0})))
      ∙ ( substComposite S0 refl (g u0) (F (uf0 u0) bP)
        ∙ cong (subst S0 (g u0))
               (substCommSlice {S = S1} {P = S0} rf F refl bP) )
twist-core-base {S1 = S1} {S0 = S0} {uf0 = uf0} {rf0 = rf0} {fX = fX} {rf = rf}
                F g u0 bP =
  lhsE ∙ sym rhsE
  where
  x : S0 (rf (uf0 u0))
  x = F (uf0 u0) bP

  G : rf (uf0 u0) ≡ rf0 (fX u0)
  G = g u0

  tS : subst S1 refl bP ≡ bP
  tS = substRefl S1 bP

  tX : subst S0 refl x ≡ x
  tX = substRefl S0 x

  tΦ : subst S0 refl (subst S0 G x) ≡ subst S0 G x
  tΦ = substRefl S0 (subst S0 G x)

  cM : {e e' : rf (uf0 u0) ≡ rf0 (fX u0)} → e ≡ e' → subst S0 e x ≡ subst S0 e' x
  cM = cong (λ e → subst S0 e x)

  Ft : x ≡ F (uf0 u0) (subst S1 refl bP)
  Ft = cong (F (uf0 u0)) (sym tS)

  cGFt : subst S0 G x ≡ subst S0 G (F (uf0 u0) (subst S1 refl bP))
  cGFt = cong (subst S0 G) Ft

  cGtX : subst S0 G (subst S0 refl x) ≡ subst S0 G x
  cGtX = cong (subst S0 G) tX

  lhsE : substComposite S0 G refl x
         ∙ substCommSlice {S = λ dd → S1 (uf0 dd)} {P = λ dd → S0 (rf0 dd)}
             fX (λ dd y → subst S0 (g dd) (F (uf0 dd) y)) refl bP
         ≡ cM (sym (rUnit G)) ∙ cGFt
  lhsE =
      cong (_∙ substCommSlice {S = λ dd → S1 (uf0 dd)}
                              {P = λ dd → S0 (rf0 dd)}
                              fX (λ dd y → subst S0 (g dd) (F (uf0 dd) y))
                              refl bP)
           (substComposite-refl S0 G x)
    ∙ cong ((cM (sym (rUnit G)) ∙ sym tΦ) ∙_)
           (substCommSlice-refl {S = λ dd → S1 (uf0 dd)}
                                {Q = λ dd → S0 (rf0 dd)}
                                fX (λ dd y → subst S0 (g dd) (F (uf0 dd) y)) bP)
    ∙ ∙-assoc (cM (sym (rUnit G))) (sym tΦ) (tΦ ∙ cGFt)
    ∙ cong (cM (sym (rUnit G)) ∙_) (∙-cancel-l tΦ cGFt)

  rhsE : cong (λ e → subst S0 e x) (sym (hnat g (refl {x = u0})))
         ∙ ( substComposite S0 refl G x
           ∙ cong (subst S0 G) (substCommSlice {S = S1} {P = S0} rf F refl bP) )
         ≡ cM (sym (rUnit G)) ∙ cGFt
  rhsE =
      cong (λ m → cM (sym m)
                  ∙ ( substComposite S0 refl G x
                    ∙ cong (subst S0 G)
                           (substCommSlice {S = S1} {P = S0} rf F refl bP) ))
           (hnat-refl g)
    ∙ cong (λ m → cM m
                  ∙ ( substComposite S0 refl G x
                    ∙ cong (subst S0 G)
                           (substCommSlice {S = S1} {P = S0} rf F refl bP) ))
           (symDistr (sym (lUnit G)) (rUnit G))
    ∙ cong (_∙ ( substComposite S0 refl G x
               ∙ cong (subst S0 G)
                      (substCommSlice {S = S1} {P = S0} rf F refl bP) ))
           (cong-∙ (λ e → subst S0 e x) (sym (rUnit G)) (lUnit G))
    ∙ cong (λ m → (cM (sym (rUnit G)) ∙ cM (lUnit G))
                  ∙ (m ∙ cong (subst S0 G)
                              (substCommSlice {S = S1} {P = S0} rf F refl bP)))
           (substComposite-lrefl S0 G x)
    ∙ cong (λ m → (cM (sym (rUnit G)) ∙ cM (lUnit G))
                  ∙ ((cM (sym (lUnit G)) ∙ cong (subst S0 G) (sym tX))
                     ∙ cong (subst S0 G) m))
           (substCommSlice-refl {S = S1} {Q = S0} rf F bP)
    ∙ cong (λ m → (cM (sym (rUnit G)) ∙ cM (lUnit G))
                  ∙ ((cM (sym (lUnit G)) ∙ cong (subst S0 G) (sym tX)) ∙ m))
           (cong-∙ (subst S0 G) tX Ft)
    ∙ cong ((cM (sym (rUnit G)) ∙ cM (lUnit G)) ∙_)
           ( ∙-assoc (cM (sym (lUnit G))) (sym cGtX) (cGtX ∙ cGFt)
           ∙ cong (cM (sym (lUnit G)) ∙_) (∙-cancel-l cGtX cGFt) )
    ∙ ∙-assoc (cM (sym (rUnit G))) (cM (lUnit G))
              (cM (sym (lUnit G)) ∙ cGFt)
    ∙ cong (cM (sym (rUnit G)) ∙_) (∙-cancel-l (cM (sym (lUnit G))) cGFt)

twist-core :
  {X1 : Set ℓ} {X0 : Set ℓ'} {TU : Set ℓ''} {T : Set ℓ'''}
  {S1 : X1 → Set ℓp} {S0 : X0 → Set ℓp}
  {uf0 : TU → X1} {rf0 : T → X0} {fX : TU → T} {rf : X1 → X0}
  (F : (y : X1) → S1 y → S0 (rf y))
  (g : (dd : TU) → rf (uf0 dd) ≡ rf0 (fX dd))
  {u0 u1 : TU} (eU : u0 ≡ u1) (bP : S1 (uf0 u0))
  → substComposite S0 (g u0) (cong (λ dd → rf0 (fX dd)) eU) (F (uf0 u0) bP)
    ∙ substCommSlice {S = λ dd → S1 (uf0 dd)} {P = λ dd → S0 (rf0 dd)}
        fX (λ dd x → subst S0 (g dd) (F (uf0 dd) x)) eU bP
    ≡ cong (λ e → subst S0 e (F (uf0 u0) bP)) (sym (hnat g eU))
      ∙ ( substComposite S0 (cong (λ dd → rf (uf0 dd)) eU) (g u1)
                         (F (uf0 u0) bP)
        ∙ cong (subst S0 (g u1))
               (substCommSlice {S = S1} {P = S0} rf F (cong uf0 eU) bP) )
twist-core {S1 = S1} {S0 = S0} {uf0 = uf0} {rf0 = rf0} {fX = fX} {rf = rf}
           F g {u0 = u0} eU bP =
  J (λ u1 eU →
       substComposite S0 (g u0) (cong (λ dd → rf0 (fX dd)) eU) (F (uf0 u0) bP)
       ∙ substCommSlice {S = λ dd → S1 (uf0 dd)} {P = λ dd → S0 (rf0 dd)}
           fX (λ dd x → subst S0 (g dd) (F (uf0 dd) x)) eU bP
       ≡ cong (λ e → subst S0 e (F (uf0 u0) bP)) (sym (hnat g eU))
         ∙ ( substComposite S0 (cong (λ dd → rf (uf0 dd)) eU) (g u1)
                            (F (uf0 u0) bP)
           ∙ cong (subst S0 (g u1))
                  (substCommSlice {S = S1} {P = S0} rf F (cong uf0 eU) bP) ))
    (twist-core-base {S1 = S1} {S0 = S0} {uf0 = uf0} {rf0 = rf0} {fX = fX}
                     {rf = rf} F g u0 bP)
    eU


twist-Sq :
  {X1 : Set ℓ} {X0 : Set ℓ'} {TU : Set ℓ''} {T : Set ℓ'''}
  {S1 : X1 → Set ℓp} {S0 : X0 → Set ℓp}
  {uf0 : TU → X1} {rf0 : T → X0} {fX : TU → T} {rf : X1 → X0}
  (F : (y : X1) → S1 y → S0 (rf y))
  (g : (dd : TU) → rf (uf0 dd) ≡ rf0 (fX dd))
  {u0 u1 : TU} (eU : u0 ≡ u1)
  {bP : S1 (uf0 u0)} {bQ : S1 (uf0 u1)}
  (inner : subst S1 (cong uf0 eU) bP ≡ bQ)
  {cA0 : S0 (rf0 (fX u0))} (kc0 : cA0 ≡ subst S0 (g u0) (F (uf0 u0) bP))
  {cA1 : S0 (rf0 (fX u1))} (kc1 : cA1 ≡ subst S0 (g u1) (F (uf0 u1) bQ))
  → Sq S0 (sym (hnat g eU))
       (_⊙_ {P = S0} {p = g u0} (sym kc0)
            {p' = cong (λ dd → rf0 (fX dd)) eU}
            ( cong (subst (λ dd → S0 (rf0 dd)) (cong fX eU)) kc0
            ∙ ( sigT-map-eq {P = λ dd → S1 (uf0 dd)} {Q = λ dd → S0 (rf0 dd)}
                            {f = fX} (λ dd x → subst S0 (g dd) (F (uf0 dd) x))
                            {p = eU} inner
              ∙ sym kc1) ))
       (_⊙_ {P = S0} {p = cong (λ dd → rf (uf0 dd)) eU}
            (sigT-map-eq {P = S1} {Q = S0} {f = rf} F {p = cong uf0 eU} inner)
            {p' = g u1} (sym kc1))
twist-Sq {S1 = S1} {S0 = S0} {uf0 = uf0} {rf0 = rf0} {fX = fX} {rf = rf}
         F g {u0 = u0} {u1 = u1} eU {bP = bP} inner kc0 kc1 =
    cong (SCL ∙_) (∙-cancel-l XK (MΦ ∙ sym kc1))
  ∙ cong (λ m → SCL ∙ (m ∙ sym kc1))
         (sigT-map-eq-decomp {S = λ dd → S1 (uf0 dd)} {Q = λ dd → S0 (rf0 dd)}
                             {f = fX} (λ dd x → subst S0 (g dd) (F (uf0 dd) x))
                             eU inner)
  ∙ cong (SCL ∙_) (∙-assoc scsΦ CΦ (sym kc1))
  ∙ sym (∙-assoc SCL scsΦ (CΦ ∙ sym kc1))
  ∙ cong (_∙ (CΦ ∙ sym kc1))
         (twist-core {S1 = S1} {S0 = S0} {uf0 = uf0} {rf0 = rf0} {fX = fX}
                     {rf = rf} F g eU bP)
  ∙ ∙-assoc cMh (SCR ∙ CF) (CΦ ∙ sym kc1)
  ∙ cong (cMh ∙_) ( ∙-assoc SCR CF (CΦ ∙ sym kc1)
                  ∙ cong (SCR ∙_) (sym (∙-assoc CF CΦ (sym kc1))) )
  ∙ cong (λ m → cMh ∙ (SCR ∙ (m ∙ sym kc1)))
         ( sym (cong-∙ (subst S0 (g u1)) scsF (cong (F (uf0 u1)) inner))
         ∙ cong (cong (subst S0 (g u1)))
                (sym (sigT-map-eq-decomp {S = S1} {Q = S0} {f = rf} F
                                         (cong uf0 eU) inner)) )
  where
  SCL : _
  SCL = substComposite S0 (g u0) (cong (λ dd → rf0 (fX dd)) eU) (F (uf0 u0) bP)

  SCR : _
  SCR = substComposite S0 (cong (λ dd → rf (uf0 dd)) eU) (g u1) (F (uf0 u0) bP)

  XK : _
  XK = cong (subst (λ dd → S0 (rf0 dd)) (cong fX eU)) kc0

  MΦ : _
  MΦ = sigT-map-eq {P = λ dd → S1 (uf0 dd)} {Q = λ dd → S0 (rf0 dd)} {f = fX}
                   (λ dd x → subst S0 (g dd) (F (uf0 dd) x)) {p = eU} inner

  scsΦ : _
  scsΦ = substCommSlice {S = λ dd → S1 (uf0 dd)} {P = λ dd → S0 (rf0 dd)}
           fX (λ dd x → subst S0 (g dd) (F (uf0 dd) x)) eU bP

  scsF : _
  scsF = substCommSlice {S = S1} {P = S0} rf F (cong uf0 eU) bP

  CΦ : _
  CΦ = cong (λ x → subst S0 (g u1) (F (uf0 u1) x)) inner

  CF : _
  CF = cong (subst S0 (g u1)) scsF

  cMh : _
  cMh = cong (λ e → subst S0 e (F (uf0 u0) bP)) (sym (hnat g eU))

------------------------------------------------------------------------
-- (v.c) Right cancellation as a J, and its whiskering round trip.
-- permutahedral-coherence's last step uses ∙-cancel-rʲ so that this round
-- trip is available to the assembly.
------------------------------------------------------------------------

whisker-cancel : {A : Set ℓ} {x y z : A} (δ : y ≡ z) {X Y : x ≡ y}
                 (E : X ∙ δ ≡ Y ∙ δ)
                 → cong (_∙ δ) (∙-cancel-rʲ δ E) ≡ E
whisker-cancel {A = A} {x = x} {y = y} δ {X} {Y} E =
  J (λ _ δ → {X Y : x ≡ y} (E : X ∙ δ ≡ Y ∙ δ)
             → cong (_∙ δ) (∙-cancel-rʲ δ E) ≡ E)
    (λ {X} {Y} E →
        cong (cong (_∙ refl))
             (cong (λ h → h {X} {Y} E)
                   (JRefl {A = A} {x = y}
                          (λ _ δ → {X Y : x ≡ y} → X ∙ δ ≡ Y ∙ δ → X ≡ Y)
                          (λ {X} {Y} E → rUnit X ∙ (E ∙ sym (rUnit Y)))))
      ∙ sym (∙-cancel-l (rUnit X) (cong (_∙ refl) (rUnit X ∙ (E ∙ sym (rUnit Y)))))
      ∙ cong (sym (rUnit X) ∙_)
             (sym (hnat {f = λ W → W} {g = λ W → W ∙ refl} rUnit
                        (rUnit X ∙ (E ∙ sym (rUnit Y)))))
      ∙ cong (sym (rUnit X) ∙_)
             ( ∙-assoc (rUnit X) (E ∙ sym (rUnit Y)) (rUnit Y)
             ∙ cong (rUnit X ∙_) ( ∙-assoc E (sym (rUnit Y)) (rUnit Y)
                                 ∙ cong (E ∙_) (lCancel (rUnit Y))
                                 ∙ sym (rUnit E) ) )
      ∙ ∙-cancel-l (rUnit X) E)
    δ E


------------------------------------------------------------------------
-- Two re-indexing lemmas for (v.d): ⊙ along a reparametrised family
-- (S0r = S0 ∘ rf0 versus S0), and sigT-map-eq along a composite map.
------------------------------------------------------------------------

⊙-reindex :
  {A' : Set ℓ} {B : Set ℓ'} (Q : B → Set ℓ'') (f : A' → B)
  {x y z : A'} {u : Q (f x)} {v : Q (f y)} {w : Q (f z)}
  {p : x ≡ y} (q : subst (λ a → Q (f a)) p u ≡ v)
  {p' : y ≡ z} (q' : subst (λ a → Q (f a)) p' v ≡ w)
  → Sq Q (cong-∙ f p p')
       (_⊙_ {P = λ a → Q (f a)} {p = p} q {p' = p'} q')
       (_⊙_ {P = Q} {p = cong f p} q {p' = cong f p'} q')
⊙-reindex Q f {u = u} {p = p} q {p' = p'} q' =
    cong (_∙ (cong (subst Q (cong f p')) q ∙ q'))
         (substComposite-cong f Q p p' u)
  ∙ ∙-assoc (cong (λ e → subst Q e u) (cong-∙ f p p'))
            (substComposite Q (cong f p) (cong f p') u)
            (cong (subst Q (cong f p')) q ∙ q')

sigT-map-eq-comp :
  {A' : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
  {S : A' → Set ℓp} {P : B → Set ℓq} {Q : C → Set ℓr}
  {f : A' → B} {h : B → C}
  (G : (a : A') → S a → P (f a)) (F : (b : B) → P b → Q (h b))
  {x y : A'} {u : S x} {v : S y} {p : x ≡ y} (k : subst S p u ≡ v)
  → sigT-map-eq {P = P} {Q = Q} {f = h} F {p = cong f p}
                (sigT-map-eq {P = S} {Q = P} {f = f} G {p = p} k)
    ≡ sigT-map-eq {P = S} {Q = Q} {f = λ a → h (f a)}
                  (λ a s → F (f a) (G a s)) {p = p} k
sigT-map-eq-comp {S = S} {P = P} {Q = Q} {f = f} {h = h} G F {p = p} k =
  cong (λ ω → fromPathP {P = λ i → Q (h (f (p i)))}
                        (λ i → F (f (p i)) (ω i)))
       (toPathP-fromPathP (λ i → P (f (p i)))
                          (λ i → G (p i) (toPathP {P = λ i → S (p i)} k i)))


------------------------------------------------------------------------
-- (v.d) The six fiber edges.  Each comes in two halves written in
-- parallel: a BASE cell (k-cell / map-cell — these are what
-- permutahedral-coherence feeds to zig3) and the fiber square over it.
------------------------------------------------------------------------

subst→Sq : {X : Set ℓ} (P : X → Set ℓ') {x z : X} {u : P x} {w : P z}
           {p p' : x ≡ z} (H : p ≡ p')
           {q : subst P p u ≡ w} {q' : subst P p' u ≡ w}
           → subst (λ π → subst P π u ≡ w) H q ≡ q' → Sq P H q q'
subst→Sq P {u = u} H {q} {q'} e =
    sym (∙-cancel-l (sym (cong (λ ee → subst P ee u) H)) q)
  ∙ cong (cong (λ ee → subst P ee u) H ∙_)
         (sym (substInPathL (cong (λ ee → subst P ee u) H) q) ∙ e)

k-edge-Sq :
  {X2 : Set ℓ} {X1 : Set ℓ'} {X0 : Set ℓ''} {T : Set ℓ'''}
  {S2 : X2 → Set ℓp} {S1 : X1 → Set ℓp} {S0 : X0 → Set ℓp}
  {rus ruq1 : X2 → X1} {rfq rfs : X1 → X0} {rf0 : T → X0}
  (Fq : (y : X1) → S1 y → S0 (rfq y)) (Fs : (y : X1) → S1 y → S0 (rfs y))
  (Rs : (z : X2) → S2 z → S1 (rus z)) (Rq1 : (z : X2) → S2 z → S1 (ruq1 z))
  {KA : (z : X2) → rfq (rus z) ≡ rfs (ruq1 z)}
  (HKA : (z : X2) (c : S2 z)
         → subst S0 (KA z) (Fq (rus z) (Rs z c)) ≡ Fs (ruq1 z) (Rq1 z c))
  {z1 z2 : X2} (pI : z1 ≡ z2) {c1 : S2 z1} {c2 : S2 z2}
  (k : c2 ≡ subst S2 pI c1)
  {d1 d2 : T} (E : d1 ≡ d2)
  {y1 y2 : X1} (pV : rus z2 ≡ y1) (pV' : ruq1 z2 ≡ y2)
  (gu : rfq y1 ≡ rf0 d1) (gv : rfs y2 ≡ rf0 d2)
  (HH : cong rfq pV ∙ (gu ∙ cong rf0 E) ≡ KA z2 ∙ (cong rfs pV' ∙ gv))
  (b : S1 y1) (kb : b ≡ subst S1 pV (Rs z2 c2))
  (b' : S1 y2) (kb' : b' ≡ subst S1 pV' (Rq1 z2 c2))
  (cc : S0 (rf0 d1)) (kc : cc ≡ subst S0 gu (Fq y1 b))
  (cc' : S0 (rf0 d2)) (kc' : cc' ≡ subst S0 gv (Fs y2 b'))
  → Sq S0 (k-cell {f = λ z → rfq (rus z)} {g = λ z → rfs (ruq1 z)} KA pI
                  (cong rfq pV) gu (cong rf0 E) (cong rfs pV') gv HH)
       (_⊙_ {P = S0}
            (_⊙_ {P = S0}
                 (sigT-map-eq {P = S1} {Q = S0} {f = rfq} Fq {p = cong rus pI}
                              (sigT-map-eq {P = S2} {Q = S1} {f = rus} Rs
                                           {p = pI} (sym k)))
                 (_⊙_ {P = S0}
                      (sigT-map-eq {P = S1} {Q = S0} {f = rfq} Fq {p = pV}
                                   (sym kb))
                      (sym kc)))
            ( cong (λ x → subst (λ dd → S0 (rf0 dd)) E x) kc
            ∙ ( cong (λ x → subst (λ dd → S0 (rf0 dd)) E
                                  (subst S0 gu (Fq y1 x))) kb
              ∙ ( rew-cohLayer33 {P = S0} {S2 = S1} {S3 = S1}
                    {rf0 = rf0} {rfF = rfq} {rfG = rfs} {F = Fq} {G = Fs}
                    {E1 = E} {C2 = pV} {D2 = pV'} {C1 = gu} {D1 = gv}
                    {K = KA z2} {aL = Rs z2 c2} {aR = Rq1 z2 c2}
                    (HKA z2 c2) HH
                ∙ ( sym (cong (λ x → subst S0 gv (Fs y2 x)) kb')
                  ∙ sym kc' )))))
       (_⊙_ {P = S0} (HKA z1 c1)
            (_⊙_ {P = S0}
                 (sigT-map-eq {P = S1} {Q = S0} {f = rfs} Fs {p = cong ruq1 pI}
                              (sigT-map-eq {P = S2} {Q = S1} {f = ruq1} Rq1
                                           {p = pI} (sym k)))
                 (_⊙_ {P = S0}
                      (sigT-map-eq {P = S1} {Q = S0} {f = rfs} Fs {p = pV'}
                                   (sym kb'))
                      (sym kc'))))
k-edge-Sq {S2 = S2} {S1 = S1} {S0 = S0} {rus = rus} {ruq1 = ruq1}
          {rfq = rfq} {rfs = rfs} {rf0 = rf0} Fq Fs Rs Rq1 {KA = KA} HKA
          {z1 = z1} {z2 = z2} pI {c1 = c1} {c2 = c2} k {d1 = d1} {d2 = d2} E
          {y1 = y1} {y2 = y2} pV pV' gu gv HH b kb b' kb' cc kc cc' kc' =
  Sq-∙ S0 s1 (Sq-∙ S0 s2 (Sq-∙ S0 s3 (Sq-∙ S0 s4 (Sq-∙ S0 s5 (Sq-∙ S0 s6 s7)))))
  where
  P₀ : _
  P₀ = sigT-map-eq {P = S1} {Q = S0} {f = rfq} Fq {p = cong rus pI}
                   (sigT-map-eq {P = S2} {Q = S1} {f = rus} Rs {p = pI} (sym k))

  Q₀ : _
  Q₀ = sigT-map-eq {P = S1} {Q = S0} {f = rfq} Fq {p = pV} (sym kb)

  N₀ : _
  N₀ = sym kc

  W : _
  W = _⊙_ {P = S0}
          (sigT-map-eq {P = S1} {Q = S0} {f = rfs} Fs {p = pV'} (sym kb'))
          (sym kc')

  MFL : _
  MFL = sigT-map-eq {P = S2} {Q = S0} {f = λ z → rfq (rus z)}
                    (λ z c → Fq (rus z) (Rs z c)) {p = pI} (sym k)

  MFR : _
  MFR = sigT-map-eq {P = S2} {Q = S0} {f = λ z → rfs (ruq1 z)}
                    (λ z c → Fs (ruq1 z) (Rq1 z c)) {p = pI} (sym k)

  Cch : _
  Cch = cong (λ x → subst (λ dd → S0 (rf0 dd)) E x) kc
      ∙ ( cong (λ x → subst (λ dd → S0 (rf0 dd)) E
                            (subst S0 gu (Fq y1 x))) kb
        ∙ ( rew-cohLayer33 {P = S0} {S2 = S1} {S3 = S1}
              {rf0 = rf0} {rfF = rfq} {rfG = rfs} {F = Fq} {G = Fs}
              {E1 = E} {C2 = pV} {D2 = pV'} {C1 = gu} {D1 = gv}
              {K = KA z2} {aL = Rs z2 c2} {aR = Rq1 z2 c2} (HKA z2 c2) HH
          ∙ ( sym (cong (λ x → subst S0 gv (Fs y2 x)) kb') ∙ sym kc' )))

  restr0Sq : Sq S0 HH (_⊙_ {P = S0} Q₀ (_⊙_ {P = S0} N₀ (refl ∙ Cch)))
                      (_⊙_ {P = S0} (HKA z2 c2) W)
  restr0Sq = subst→Sq S0 HH
    (rew-coh2Painting-restr0-gen {P = S0} {S2 = S1} {S3 = S1}
       {rq = rfq} {rr = rfs} {r0 = rf0} Fq Fs E pV pV' gu gv (KA z2)
       c2 (Rs z2) (Rq1 z2) (HKA z2 c2) HH b kb b' kb' cc kc cc' kc')

  inner1 : Sq S0 (refl ∙ HH) (_⊙_ {P = S0} Q₀ (_⊙_ {P = S0} N₀ Cch))
                             (_⊙_ {P = S0} (HKA z2 c2) W)
  inner1 = Sq-∙ S0
    (Sq-of-≡ S0 (cong (λ m → _⊙_ {P = S0} Q₀ (_⊙_ {P = S0} N₀ m)) (lUnit Cch)))
    restr0Sq

  s1 : _
  s1 = ⊙-assoc-Sq S0 P₀ (_⊙_ {P = S0} Q₀ N₀) Cch

  s2 : _
  s2 = ⊙-whisker-r S0 P₀ (⊙-assoc-Sq S0 Q₀ N₀ Cch)

  s3 : _
  s3 = ⊙-whisker-r S0 P₀ inner1

  s4 : _
  s4 = Sq-sym S0 (⊙-assoc-Sq S0 P₀ (HKA z2 c2) W)

  s5 : _
  s5 = ⊙-whisker-l S0 W
         (Sq-∙ S0
            (Sq-of-≡ S0 (cong (λ m → _⊙_ {P = S0} m (HKA z2 c2))
                              (sigT-map-eq-comp {S = S2} {P = S1} {Q = S0}
                                                {f = rus} {h = rfq}
                                                Rs Fq (sym k))))
            (family-Sq {S2 = S2} {S0 = S0} {fL = λ z → rfq (rus z)}
                       {fR = λ z → rfs (ruq1 z)}
                       (λ z c → Fq (rus z) (Rs z c))
                       (λ z c → Fs (ruq1 z) (Rq1 z c)) KA HKA pI (sym k)))

  s6 : _
  s6 = ⊙-assoc-Sq S0 (HKA z1 c1) MFR W

  s7 : _
  s7 = Sq-of-≡ S0 (cong (λ m → _⊙_ {P = S0} (HKA z1 c1) (_⊙_ {P = S0} m W))
                        (sym (sigT-map-eq-comp {S = S2} {P = S1} {Q = S0}
                                               {f = ruq1} {h = rfs}
                                               Rq1 Fs (sym k))))


map-edge-Sq :
  {X2 : Set ℓ} {X1 : Set ℓ'} {X0 : Set ℓ''} {TU : Set ℓ'''} {T : Set ℓq}
  {A0 : Set ℓr}
  {S2 : X2 → Set ℓp} {S1 : X1 → Set ℓp} {S0 : X0 → Set ℓp}
  {rur rus : X2 → X1} {uf0 : TU → X1} {rf : X1 → X0} {rf0 : T → X0}
  {fX : TU → T}
  (Rr : (z : X2) → S2 z → S1 (rur z)) (Rs : (z : X2) → S2 z → S1 (rus z))
  (F : (y : X1) → S1 y → S0 (rf y))
  (g : (dd : TU) → rf (uf0 dd) ≡ rf0 (fX dd))
  {zs1 zs2 zr1 zr2 : X2} (pIs : zs1 ≡ zs2) (pIr : zr1 ≡ zr2)
  {u0 u1 : TU} (eU : u0 ≡ u1)
  (pV0 : rur zs2 ≡ uf0 u0) (pV1 : rus zr2 ≡ uf0 u1)
  (K : rur zs1 ≡ rus zr1)
  (HH : cong rur pIs ∙ (pV0 ∙ cong uf0 eU) ≡ K ∙ (cong rus pIr ∙ pV1))
  (a : A0) (FIs : A0 → S2 zs1) (FIr : A0 → S2 zr1)
  (HK : subst S1 K (Rr zs1 (FIs a)) ≡ Rs zr1 (FIr a))
  (aP : S2 zs2) (kP : aP ≡ subst S2 pIs (FIs a))
  (aQ : S2 zr2) (kQ : aQ ≡ subst S2 pIr (FIr a))
  (bP : S1 (uf0 u0)) (kbP : bP ≡ subst S1 pV0 (Rr zs2 aP))
  (bQ : S1 (uf0 u1)) (kbQ : bQ ≡ subst S1 pV1 (Rs zr2 aQ))
  (cA0 : S0 (rf0 (fX u0))) (kc0 : cA0 ≡ subst S0 (g u0) (F (uf0 u0) bP))
  (cA1 : S0 (rf0 (fX u1))) (kc1 : cA1 ≡ subst S0 (g u1) (F (uf0 u1) bQ))
  → Sq S0 (map-cell {rur = rur} {rus = rus} {uf0 = uf0} {rf = rf}
                    {rf0 = rf0} {fX = fX} g pIs pIr eU pV0 pV1 K HH)
       (_⊙_ {P = S0}
            (_⊙_ {P = S0}
                 (sigT-map-eq {P = S1} {Q = S0} {f = rf} F {p = cong rur pIs}
                    (sigT-map-eq {P = S2} {Q = S1} {f = rur} Rr {p = pIs}
                                 (sym kP)))
                 (_⊙_ {P = S0}
                      (sigT-map-eq {P = S1} {Q = S0} {f = rf} F {p = pV0}
                                   (sym kbP))
                      (sym kc0)))
            ( cong (λ x → subst (λ dd → S0 (rf0 dd)) (cong fX eU) x) kc0
            ∙ ( sigT-map-eq {P = λ dd → S1 (uf0 dd)} {Q = λ dd → S0 (rf0 dd)}
                            {f = fX} (λ dd x → subst S0 (g dd) (F (uf0 dd) x))
                            {p = eU}
                            ( cong (λ x → subst (λ dd → S1 (uf0 dd)) eU x) kbP
                            ∙ ( cong (λ x → subst (λ dd → S1 (uf0 dd)) eU
                                                  (subst S1 pV0 (Rr zs2 x))) kP
                              ∙ ( rew-cohLayer33 {P = S1} {S2 = S2} {S3 = S2}
                                    {rf0 = uf0} {rfF = rur} {rfG = rus}
                                    {F = Rr} {G = Rs} {E1 = eU} {C2 = pIs}
                                    {D2 = pIr} {C1 = pV0} {D1 = pV1} {K = K}
                                    {aL = FIs a} {aR = FIr a} HK HH
                                  ∙ ( sym (cong (λ x → subst S1 pV1 (Rs zr2 x))
                                                kQ)
                                    ∙ sym kbQ ))))
              ∙ sym kc1 )))
       (_⊙_ {P = S0}
            (sigT-map-eq {P = S1} {Q = S0} {f = rf} F {p = K} HK)
            (_⊙_ {P = S0}
                 (sigT-map-eq {P = S1} {Q = S0} {f = rf} F {p = cong rus pIr}
                    (sigT-map-eq {P = S2} {Q = S1} {f = rus} Rs {p = pIr}
                                 (sym kQ)))
                 (_⊙_ {P = S0}
                      (sigT-map-eq {P = S1} {Q = S0} {f = rf} F {p = pV1}
                                   (sym kbQ))
                      (sym kc1))))
map-edge-Sq {X1 = X1} {S2 = S2} {S1 = S1} {S0 = S0} {rur = rur} {rus = rus}
            {uf0 = uf0} {rf = rf} {rf0 = rf0} {fX = fX}
            Rr Rs F g {zs1 = zs1} {zs2 = zs2} {zr1 = zr1} {zr2 = zr2} pIs pIr
            {u0 = u0} {u1 = u1} eU pV0 pV1 K HH a FIs FIr HK aP kP aQ kQ
            bP kbP bQ kbQ cA0 kc0 cA1 kc1 =
  Sq-∙ S0 t1 (Sq-∙ S0 t2 (Sq-∙ S0 t3 (Sq-∙ S0 t4 (Sq-∙ S0 t5
    (Sq-∙ S0 t6 (Sq-∙ S0 t7 (Sq-∙ S0 t8 (Sq-∙ S0 t9 (Sq-∙ S0 t10
      (Sq-∙ S0 t11 (Sq-∙ S0 t12 t13)))))))))))
  where
  MF : {y1 y2 : X1} {v1 : S1 y1} {v2 : S1 y2} (p : y1 ≡ y2)
       → subst S1 p v1 ≡ v2 → subst S0 (cong rf p) (F y1 v1) ≡ F y2 v2
  MF p x = sigT-map-eq {P = S1} {Q = S0} {f = rf} F {p = p} x

  INNER : _
  INNER = cong (λ x → subst (λ dd → S1 (uf0 dd)) eU x) kbP
          ∙ ( cong (λ x → subst (λ dd → S1 (uf0 dd)) eU
                                (subst S1 pV0 (Rr zs2 x))) kP
            ∙ ( rew-cohLayer33 {P = S1} {S2 = S2} {S3 = S2}
                  {rf0 = uf0} {rfF = rur} {rfG = rus} {F = Rr} {G = Rs}
                  {E1 = eU} {C2 = pIs} {D2 = pIr} {C1 = pV0} {D1 = pV1}
                  {K = K} {aL = FIs a} {aR = FIr a} HK HH
              ∙ ( sym (cong (λ x → subst S1 pV1 (Rs zr2 x)) kQ) ∙ sym kbQ )))

  C1 : _
  C1 = cong (λ x → subst (λ dd → S0 (rf0 dd)) (cong fX eU) x) kc0
       ∙ ( sigT-map-eq {P = λ dd → S1 (uf0 dd)} {Q = λ dd → S0 (rf0 dd)}
                       {f = fX} (λ dd x → subst S0 (g dd) (F (uf0 dd) x))
                       {p = eU} INNER
         ∙ sym kc1 )

  P₀ : _
  P₀ = MF (cong rur pIs)
          (sigT-map-eq {P = S2} {Q = S1} {f = rur} Rr {p = pIs} (sym kP))

  Q₀ : _
  Q₀ = MF pV0 (sym kbP)

  N₀ : _
  N₀ = sym kc0

  MI : _
  MI = MF (cong uf0 eU) INNER

  L1 : Sq S1 HH
         (_⊙_ {P = S1}
              (sigT-map-eq {P = S2} {Q = S1} {f = rur} Rr {p = pIs} (sym kP))
              (_⊙_ {P = S1} (sym kbP) (refl ∙ INNER)))
         (_⊙_ {P = S1} HK
              (_⊙_ {P = S1}
                   (sigT-map-eq {P = S2} {Q = S1} {f = rus} Rs {p = pIr}
                                (sym kQ))
                   (sym kbQ)))
  L1 = subst→Sq S1 HH
    (rew-coh2Painting-restr0-gen {P = S1} {S2 = S2} {S3 = S2}
       {rq = rur} {rr = rus} {r0 = uf0} Rr Rs eU pIs pIr pV0 pV1 K
       a FIs FIr HK HH aP kP aQ kQ bP kbP bQ kbQ)

  t1 : _
  t1 = ⊙-assoc-Sq S0 P₀ (_⊙_ {P = S0} Q₀ N₀) C1

  t2 : _
  t2 = ⊙-whisker-r S0 P₀ (⊙-assoc-Sq S0 Q₀ N₀ C1)

  t3 : _
  t3 = ⊙-whisker-r S0 P₀ (⊙-whisker-r S0 Q₀
         (twist-Sq {S1 = S1} {S0 = S0} {uf0 = uf0} {rf0 = rf0} {fX = fX}
                   {rf = rf} F g eU INNER kc0 kc1))

  t4 : _
  t4 = ⊙-whisker-r S0 P₀ (Sq-sym S0 (⊙-assoc-Sq S0 Q₀ MI (sym kc1)))

  t5 : _
  t5 = ⊙-whisker-r S0 P₀ (⊙-whisker-l S0 (sym kc1)
         (Sq-sym S0 (sigT-map-eq-⊙ {S = S1} {Q = S0} {f = rf} F
                                   {p = pV0} (sym kbP)
                                   {p' = cong uf0 eU} INNER)))

  t6 : _
  t6 = Sq-sym S0 (⊙-assoc-Sq S0 P₀
         (MF (pV0 ∙ cong uf0 eU) (_⊙_ {P = S1} (sym kbP) INNER)) (sym kc1))

  t7 : _
  t7 = ⊙-whisker-l S0 (sym kc1)
         (Sq-sym S0 (sigT-map-eq-⊙ {S = S1} {Q = S0} {f = rf} F
            {p = cong rur pIs}
            (sigT-map-eq {P = S2} {Q = S1} {f = rur} Rr {p = pIs} (sym kP))
            {p' = pV0 ∙ cong uf0 eU} (_⊙_ {P = S1} (sym kbP) INNER)))

  t8 : _
  t8 = ⊙-whisker-l S0 (sym kc1)
         (Sq-of-≡ S0 (cong (λ m → MF (cong rur pIs ∙ (pV0 ∙ cong uf0 eU))
                                     (_⊙_ {P = S1}
                                          (sigT-map-eq {P = S2} {Q = S1}
                                                       {f = rur} Rr {p = pIs}
                                                       (sym kP))
                                          (_⊙_ {P = S1} (sym kbP) m)))
                           (lUnit INNER)))

  t9 : _
  t9 = ⊙-whisker-l S0 (sym kc1)
         (sigT-map-eq-Sq {S = S1} {Q = S0} {f = rf} F L1)

  t10 : _
  t10 = ⊙-whisker-l S0 (sym kc1)
          (sigT-map-eq-⊙ {S = S1} {Q = S0} {f = rf} F {p = K} HK
             {p' = cong rus pIr ∙ pV1}
             (_⊙_ {P = S1}
                  (sigT-map-eq {P = S2} {Q = S1} {f = rus} Rs {p = pIr}
                               (sym kQ))
                  (sym kbQ)))

  t11 : _
  t11 = ⊙-whisker-l S0 (sym kc1)
          (⊙-whisker-r S0 (MF K HK)
             (sigT-map-eq-⊙ {S = S1} {Q = S0} {f = rf} F
                {p = cong rus pIr}
                (sigT-map-eq {P = S2} {Q = S1} {f = rus} Rs {p = pIr} (sym kQ))
                {p' = pV1} (sym kbQ)))

  t12 : _
  t12 = ⊙-assoc-Sq S0 (MF K HK)
          (_⊙_ {P = S0}
               (MF (cong rus pIr)
                   (sigT-map-eq {P = S2} {Q = S1} {f = rus} Rs {p = pIr}
                                (sym kQ)))
               (MF pV1 (sym kbQ)))
          (sym kc1)

  t13 : _
  t13 = ⊙-whisker-r S0 (MF K HK)
          (⊙-assoc-Sq S0
             (MF (cong rus pIr)
                 (sigT-map-eq {P = S2} {Q = S1} {f = rus} Rs {p = pIr}
                              (sym kQ)))
             (MF pV1 (sym kbQ)) (sym kc1))


------------------------------------------------------------------------
-- rew_coh2Layer: the proof of rew-coh2Layer-Type.
------------------------------------------------------------------------

rew-coh2Layer :
  {X2 : Set ℓ} {X1 : Set ℓ'} {X0 : Set ℓ''}
  {S2 : X2 → Set ℓp} {S1 : X1 → Set ℓp} {S0 : X0 → Set ℓp}
  {TU : Set ℓ'''} {T : Set ℓq}
  {uf0 : TU → X1} {rf0 : T → X0}
  {fA fB fC : TU → T}
  {rfq rfs rfr : X1 → X0}
  {Fq : (y : X1) → S1 y → S0 (rfq y)}
  {Fs : (y : X1) → S1 y → S0 (rfs y)}
  {Fr : (y : X1) → S1 y → S0 (rfr y)}
  {gq : (dd : TU) → rfq (uf0 dd) ≡ rf0 (fA dd)}
  {gs : (dd : TU) → rfs (uf0 dd) ≡ rf0 (fB dd)}
  {gr : (dd : TU) → rfr (uf0 dd) ≡ rf0 (fC dd)}
  {rur rus ruq1 rur1 : X2 → X1}
  {Rr : (z : X2) → S2 z → S1 (rur z)}
  {Rs : (z : X2) → S2 z → S1 (rus z)}
  {Rq1 : (z : X2) → S2 z → S1 (ruq1 z)}
  {Rr1 : (z : X2) → S2 z → S1 (rur1 z)}
  {KA2 : (z : X2) → rfq (rus z) ≡ rfs (ruq1 z)}
  {KA4 : (z : X2) → rfq (rur z) ≡ rfr (ruq1 z)}
  {KA6 : (z : X2) → rfr (rus z) ≡ rfs (rur1 z)}
  {HKA2 : (z : X2) (c : S2 z)
          → subst S0 (KA2 z) (Fq (rus z) (Rs z c)) ≡ Fs (ruq1 z) (Rq1 z c)}
  {HKA4 : (z : X2) (c : S2 z)
          → subst S0 (KA4 z) (Fq (rur z) (Rr z c)) ≡ Fr (ruq1 z) (Rq1 z c)}
  {HKA6 : (z : X2) (c : S2 z)
          → subst S0 (KA6 z) (Fr (rus z) (Rs z c)) ≡ Fs (rur1 z) (Rr1 z c)}
  {A0 : Set ℓr} {a : A0}
  (u0 u1 u2 u3 u4 u5 : TU)
  (eU1 : u0 ≡ u1) (eU2 : u2 ≡ u3) (eU3 : u4 ≡ u5)
  (e2 : fA u1 ≡ fB u2) (e4 : fA u0 ≡ fC u4) (e6 : fC u5 ≡ fB u3)
  (zs1 zs2 zr1 zr2 zq1 zq2 : X2)
  (pIs : zs1 ≡ zs2) (pIr : zr1 ≡ zr2) (pIq : zq1 ≡ zq2)
  (FIs : A0 → S2 zs1) (FIr : A0 → S2 zr1) (FIq : A0 → S2 zq1)
  (pV0 : rur zs2 ≡ uf0 u0) (pV1 : rus zr2 ≡ uf0 u1)
  (pV2 : ruq1 zr2 ≡ uf0 u2) (pV3 : rur1 zq2 ≡ uf0 u3)
  (pV4 : ruq1 zs2 ≡ uf0 u4) (pV5 : rus zq2 ≡ uf0 u5)
  (K1 : rur zs1 ≡ rus zr1) (K3 : ruq1 zr1 ≡ rur1 zq1)
  (K5 : ruq1 zs1 ≡ rus zq1)
  (HK1 : subst S1 K1 (Rr zs1 (FIs a)) ≡ Rs zr1 (FIr a))
  (HK3 : subst S1 K3 (Rq1 zr1 (FIr a)) ≡ Rr1 zq1 (FIq a))
  (HK5 : subst S1 K5 (Rq1 zs1 (FIs a)) ≡ Rs zq1 (FIq a))
  (HH1 : cong rur pIs ∙ (pV0 ∙ cong uf0 eU1)
         ≡ K1 ∙ (cong rus pIr ∙ pV1))
  (HH3 : cong ruq1 pIr ∙ (pV2 ∙ cong uf0 eU2)
         ≡ K3 ∙ (cong rur1 pIq ∙ pV3))
  (HH5 : cong ruq1 pIs ∙ (pV4 ∙ cong uf0 eU3)
         ≡ K5 ∙ (cong rus pIq ∙ pV5))
  (HH2 : cong rfq pV1 ∙ (gq u1 ∙ cong rf0 e2)
         ≡ KA2 zr2 ∙ (cong rfs pV2 ∙ gs u2))
  (HH4 : cong rfq pV0 ∙ (gq u0 ∙ cong rf0 e4)
         ≡ KA4 zs2 ∙ (cong rfr pV4 ∙ gr u4))
  (HH6 : cong rfr pV5 ∙ (gr u5 ∙ cong rf0 e6)
         ≡ KA6 zq2 ∙ (cong rfs pV3 ∙ gs u3))
  (aP : S2 zs2) (kP : aP ≡ subst S2 pIs (FIs a))
  (aQ : S2 zr2) (kQ : aQ ≡ subst S2 pIr (FIr a))
  (aR : S2 zq2) (kR : aR ≡ subst S2 pIq (FIq a))
  (bP : S1 (uf0 u0)) (kbP : bP ≡ subst S1 pV0 (Rr zs2 aP))
  (bQ : S1 (uf0 u1)) (kbQ : bQ ≡ subst S1 pV1 (Rs zr2 aQ))
  (bR : S1 (uf0 u2)) (kbR : bR ≡ subst S1 pV2 (Rq1 zr2 aQ))
  (bR' : S1 (uf0 u3)) (kbR' : bR' ≡ subst S1 pV3 (Rr1 zq2 aR))
  (bW : S1 (uf0 u4)) (kbW : bW ≡ subst S1 pV4 (Rq1 zs2 aP))
  (bW' : S1 (uf0 u5)) (kbW' : bW' ≡ subst S1 pV5 (Rs zq2 aR))
  (cA0 : S0 (rf0 (fA u0))) (kc0 : cA0 ≡ subst S0 (gq u0) (Fq (uf0 u0) bP))
  (cA1 : S0 (rf0 (fA u1))) (kc1 : cA1 ≡ subst S0 (gq u1) (Fq (uf0 u1) bQ))
  (cB2 : S0 (rf0 (fB u2))) (kc2 : cB2 ≡ subst S0 (gs u2) (Fs (uf0 u2) bR))
  (cB3 : S0 (rf0 (fB u3))) (kc3 : cB3 ≡ subst S0 (gs u3) (Fs (uf0 u3) bR'))
  (cC4 : S0 (rf0 (fC u4))) (kc4 : cC4 ≡ subst S0 (gr u4) (Fr (uf0 u4) bW))
  (cC5 : S0 (rf0 (fC u5))) (kc5 : cC5 ≡ subst S0 (gr u5) (Fr (uf0 u5) bW'))
  (κ : cong fA eU1 ∙ (e2 ∙ cong fB eU2) ≡ e4 ∙ (cong fC eU3 ∙ e6))
  (HHA : cong rfq K1 ∙ (KA2 zr1 ∙ cong rfs K3)
         ≡ KA4 zs1 ∙ (cong rfr K5 ∙ KA6 zq1))
  (Hcoh2Painting :
    subst (λ π → subst S0 π (Fq (rur zs1) (Rr zs1 (FIs a)))
                 ≡ Fs (rur1 zq1) (Rr1 zq1 (FIq a))) HHA
      (_⊙_ {P = S0} {p = cong rfq K1}
           (sigT-map-eq {P = S1} {Q = S0} {f = rfq} Fq {p = K1} HK1)
           {p' = KA2 zr1 ∙ cong rfs K3}
           (_⊙_ {P = S0} {p = KA2 zr1} (HKA2 zr1 (FIr a))
                {p' = cong rfs K3}
                (sigT-map-eq {P = S1} {Q = S0} {f = rfs} Fs {p = K3} HK3)))
    ≡ _⊙_ {P = S0} {p = KA4 zs1} (HKA4 zs1 (FIs a))
          {p' = cong rfr K5 ∙ KA6 zq1}
          (_⊙_ {P = S0} {p = cong rfr K5}
               (sigT-map-eq {P = S1} {Q = S0} {f = rfr} Fr {p = K5} HK5)
               {p' = KA6 zq1} (HKA6 zq1 (FIq a))))
  (Hcoh3Frame :
    HHA ≡ permutahedral-coherence {uf0 = uf0} {rf0 = rf0}
            {fA = fA} {fB = fB} {fC = fC}
            {rfq = rfq} {rfs = rfs} {rfr = rfr}
            {gq = gq} {gs = gs} {gr = gr}
            {rur = rur} {rus = rus} {ruq1 = ruq1} {rur1 = rur1}
            {KA2 = KA2} {KA4 = KA4} {KA6 = KA6}
            u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6
            zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq
            pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5
            HH1 HH3 HH5 HH2 HH4 HH6 κ)
  → rew-coh2Layer-Type
      {X2 = X2} {X1 = X1} {X0 = X0} {S2 = S2} {S1 = S1} {S0 = S0}
      {TU = TU} {T = T} {uf0 = uf0} {rf0 = rf0}
      {fA = fA} {fB = fB} {fC = fC} {rfq = rfq} {rfs = rfs} {rfr = rfr}
      {Fq = Fq} {Fs = Fs} {Fr = Fr} {gq = gq} {gs = gs} {gr = gr}
      {rur = rur} {rus = rus} {ruq1 = ruq1} {rur1 = rur1}
      {Rr = Rr} {Rs = Rs} {Rq1 = Rq1} {Rr1 = Rr1}
      {KA2 = KA2} {KA4 = KA4} {KA6 = KA6}
      {HKA2 = HKA2} {HKA4 = HKA4} {HKA6 = HKA6} {A0 = A0} {a = a}
      u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6
      zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq FIs FIr FIq
      pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5 HK1 HK3 HK5
      HH1 HH3 HH5 HH2 HH4 HH6
      aP kP aQ kQ aR kR bP kbP bQ kbQ bR kbR bR' kbR' bW kbW bW' kbW'
      cA0 kc0 cA1 kc1 cB2 kc2 cB3 kc3 cC4 kc4 cC5 kc5
      κ HHA Hcoh2Painting Hcoh3Frame
rew-coh2Layer
  {X2 = X2} {X1 = X1} {X0 = X0} {S2 = S2} {S1 = S1} {S0 = S0}
  {TU = TU} {T = T} {uf0 = uf0} {rf0 = rf0}
  {fA = fA} {fB = fB} {fC = fC} {rfq = rfq} {rfs = rfs} {rfr = rfr}
  {Fq = Fq} {Fs = Fs} {Fr = Fr} {gq = gq} {gs = gs} {gr = gr}
  {rur = rur} {rus = rus} {ruq1 = ruq1} {rur1 = rur1}
  {Rr = Rr} {Rs = Rs} {Rq1 = Rq1} {Rr1 = Rr1}
  {KA2 = KA2} {KA4 = KA4} {KA6 = KA6}
  {HKA2 = HKA2} {HKA4 = HKA4} {HKA6 = HKA6} {A0 = A0} {a = a}
  u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6
  zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq FIs FIr FIq
  pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5 HK1 HK3 HK5
  HH1 HH3 HH5 HH2 HH4 HH6
  aP kP aQ kQ aR kR bP kbP bQ kbQ bR kbR bR' kbR' bW kbW bW' kbW'
  cA0 kc0 cA1 kc1 cB2 kc2 cB3 kc3 cC4 kc4 cC5 kc5
  κ HHA Hcoh2Painting Hcoh3Frame =
  Sq→subst S0r κ FINAL
  where
  S0r : T → Set _
  S0r dd = S0 (rf0 dd)

  S1u : TU → Set _
  S1u dd = S1 (uf0 dd)

  C1comp : subst S0r (cong fA eU1) cA0 ≡ cA1
  C1comp =
    cong (λ x → subst S0r (cong fA eU1) x) kc0
    ∙ (sigT-map-eq {P = S1u} {Q = S0r} {f = fA}
         (λ dd x → subst S0 (gq dd) (Fq (uf0 dd) x)) {p = eU1}
         (cong (λ x → subst S1u eU1 x) kbP
          ∙ (cong (λ x → subst S1u eU1 (subst S1 pV0 (Rr zs2 x))) kP
             ∙ (rew-cohLayer33 {P = S1} {S2 = S2} {S3 = S2}
                  {rf0 = uf0} {rfF = rur} {rfG = rus} {F = Rr} {G = Rs}
                  {E1 = eU1} {C2 = pIs} {D2 = pIr} {C1 = pV0} {D1 = pV1}
                  {K = K1} {aL = FIs a} {aR = FIr a} HK1 HH1
                ∙ (sym (cong (λ x → subst S1 pV1 (Rs zr2 x)) kQ)
                   ∙ sym kbQ))))
       ∙ sym kc1)

  C2comp : subst S0r e2 cA1 ≡ cB2
  C2comp =
    cong (λ x → subst S0r e2 x) kc1
    ∙ (cong (λ x → subst S0r e2 (subst S0 (gq u1) (Fq (uf0 u1) x))) kbQ
       ∙ (rew-cohLayer33 {P = S0} {S2 = S1} {S3 = S1}
            {rf0 = rf0} {rfF = rfq} {rfG = rfs} {F = Fq} {G = Fs}
            {E1 = e2} {C2 = pV1} {D2 = pV2} {C1 = gq u1} {D1 = gs u2}
            {K = KA2 zr2} {aL = Rs zr2 aQ} {aR = Rq1 zr2 aQ}
            (HKA2 zr2 aQ) HH2
          ∙ (sym (cong (λ x → subst S0 (gs u2) (Fs (uf0 u2) x)) kbR)
             ∙ sym kc2)))

  C3comp : subst S0r (cong fB eU2) cB2 ≡ cB3
  C3comp =
    cong (λ x → subst S0r (cong fB eU2) x) kc2
    ∙ (sigT-map-eq {P = S1u} {Q = S0r} {f = fB}
         (λ dd x → subst S0 (gs dd) (Fs (uf0 dd) x)) {p = eU2}
         (cong (λ x → subst S1u eU2 x) kbR
          ∙ (cong (λ x → subst S1u eU2 (subst S1 pV2 (Rq1 zr2 x))) kQ
             ∙ (rew-cohLayer33 {P = S1} {S2 = S2} {S3 = S2}
                  {rf0 = uf0} {rfF = ruq1} {rfG = rur1} {F = Rq1} {G = Rr1}
                  {E1 = eU2} {C2 = pIr} {D2 = pIq} {C1 = pV2} {D1 = pV3}
                  {K = K3} {aL = FIr a} {aR = FIq a} HK3 HH3
                ∙ (sym (cong (λ x → subst S1 pV3 (Rr1 zq2 x)) kR)
                   ∙ sym kbR'))))
       ∙ sym kc3)

  C4comp : subst S0r e4 cA0 ≡ cC4
  C4comp =
    cong (λ x → subst S0r e4 x) kc0
    ∙ (cong (λ x → subst S0r e4 (subst S0 (gq u0) (Fq (uf0 u0) x))) kbP
       ∙ (rew-cohLayer33 {P = S0} {S2 = S1} {S3 = S1}
            {rf0 = rf0} {rfF = rfq} {rfG = rfr} {F = Fq} {G = Fr}
            {E1 = e4} {C2 = pV0} {D2 = pV4} {C1 = gq u0} {D1 = gr u4}
            {K = KA4 zs2} {aL = Rr zs2 aP} {aR = Rq1 zs2 aP}
            (HKA4 zs2 aP) HH4
          ∙ (sym (cong (λ x → subst S0 (gr u4) (Fr (uf0 u4) x)) kbW)
             ∙ sym kc4)))

  C5comp : subst S0r (cong fC eU3) cC4 ≡ cC5
  C5comp =
    cong (λ x → subst S0r (cong fC eU3) x) kc4
    ∙ (sigT-map-eq {P = S1u} {Q = S0r} {f = fC}
         (λ dd x → subst S0 (gr dd) (Fr (uf0 dd) x)) {p = eU3}
         (cong (λ x → subst S1u eU3 x) kbW
          ∙ (cong (λ x → subst S1u eU3 (subst S1 pV4 (Rq1 zs2 x))) kP
             ∙ (rew-cohLayer33 {P = S1} {S2 = S2} {S3 = S2}
                  {rf0 = uf0} {rfF = ruq1} {rfG = rus} {F = Rq1} {G = Rs}
                  {E1 = eU3} {C2 = pIs} {D2 = pIq} {C1 = pV4} {D1 = pV5}
                  {K = K5} {aL = FIs a} {aR = FIq a} HK5 HH5
                ∙ (sym (cong (λ x → subst S1 pV5 (Rs zq2 x)) kR)
                   ∙ sym kbW'))))
       ∙ sym kc5)

  C6comp : subst S0r e6 cC5 ≡ cB3
  C6comp =
    cong (λ x → subst S0r e6 x) kc5
    ∙ (cong (λ x → subst S0r e6 (subst S0 (gr u5) (Fr (uf0 u5) x))) kbW'
       ∙ (rew-cohLayer33 {P = S0} {S2 = S1} {S3 = S1}
            {rf0 = rf0} {rfF = rfr} {rfG = rfs} {F = Fr} {G = Fs}
            {E1 = e6} {C2 = pV5} {D2 = pV3} {C1 = gr u5} {D1 = gs u3}
            {K = KA6 zq2} {aL = Rs zq2 aR} {aR = Rr1 zq2 aR}
            (HKA6 zq2 aR) HH6
          ∙ (sym (cong (λ x → subst S0 (gs u3) (Fs (uf0 u3) x)) kbR')
             ∙ sym kc3)))

  -- base-level copies of permutahedral-coherence's internals
  α : rfq (rur zs1) ≡ rf0 (fA u0)
  α = cong rfq (cong rur pIs) ∙ (cong rfq pV0 ∙ gq u0)

  β : rfq (rus zr1) ≡ rf0 (fA u1)
  β = cong rfq (cong rus pIr) ∙ (cong rfq pV1 ∙ gq u1)

  γ : rfs (ruq1 zr1) ≡ rf0 (fB u2)
  γ = cong rfs (cong ruq1 pIr) ∙ (cong rfs pV2 ∙ gs u2)

  δ : rfs (rur1 zq1) ≡ rf0 (fB u3)
  δ = cong rfs (cong rur1 pIq) ∙ (cong rfs pV3 ∙ gs u3)

  ε : rfr (ruq1 zs1) ≡ rf0 (fC u4)
  ε = cong rfr (cong ruq1 pIs) ∙ (cong rfr pV4 ∙ gr u4)

  ζ : rfr (rus zq1) ≡ rf0 (fC u5)
  ζ = cong rfr (cong rus pIq) ∙ (cong rfr pV5 ∙ gr u5)

  EA : rf0 (fA u0) ≡ rf0 (fA u1)
  EA = cong (λ dd → rf0 (fA dd)) eU1

  EB : rf0 (fB u2) ≡ rf0 (fB u3)
  EB = cong (λ dd → rf0 (fB dd)) eU2

  EC : rf0 (fC u4) ≡ rf0 (fC u5)
  EC = cong (λ dd → rf0 (fC dd)) eU3

  E2' : rf0 (fA u1) ≡ rf0 (fB u2)
  E2' = cong rf0 e2

  E4' : rf0 (fA u0) ≡ rf0 (fC u4)
  E4' = cong rf0 e4

  E6' : rf0 (fC u5) ≡ rf0 (fB u3)
  E6' = cong rf0 e6

  A1 : α ∙ EA ≡ cong rfq K1 ∙ β
  A1 = map-cell {rur = rur} {rus = rus} {uf0 = uf0} {rf = rfq} {rf0 = rf0}
                {fX = fA} gq pIs pIr eU1 pV0 pV1 K1 HH1

  A2 : β ∙ E2' ≡ KA2 zr1 ∙ γ
  A2 = k-cell {f = λ z → rfq (rus z)} {g = λ z → rfs (ruq1 z)}
              KA2 pIr (cong rfq pV1) (gq u1) (cong rf0 e2)
              (cong rfs pV2) (gs u2) HH2

  A3 : γ ∙ EB ≡ cong rfs K3 ∙ δ
  A3 = map-cell {rur = ruq1} {rus = rur1} {uf0 = uf0} {rf = rfs} {rf0 = rf0}
                {fX = fB} gs pIr pIq eU2 pV2 pV3 K3 HH3

  A4 : α ∙ E4' ≡ KA4 zs1 ∙ ε
  A4 = k-cell {f = λ z → rfq (rur z)} {g = λ z → rfr (ruq1 z)}
              KA4 pIs (cong rfq pV0) (gq u0) (cong rf0 e4)
              (cong rfr pV4) (gr u4) HH4

  A5 : ε ∙ EC ≡ cong rfr K5 ∙ ζ
  A5 = map-cell {rur = ruq1} {rus = rus} {uf0 = uf0} {rf = rfr} {rf0 = rf0}
                {fX = fC} gr pIs pIq eU3 pV4 pV5 K5 HH5

  A6 : ζ ∙ E6' ≡ KA6 zq1 ∙ δ
  A6 = k-cell {f = λ z → rfr (rus z)} {g = λ z → rfs (rur1 z)}
              KA6 pIq (cong rfr pV5) (gr u5) (cong rf0 e6)
              (cong rfs pV3) (gs u3) HH6

  cellL : cong rf0 (cong fA eU1 ∙ (e2 ∙ cong fB eU2))
          ≡ EA ∙ (E2' ∙ EB)
  cellL = cong-tri rf0 (cong fA eU1) e2 (cong fB eU2)

  cellR : cong rf0 (e4 ∙ (cong fC eU3 ∙ e6)) ≡ E4' ∙ (EC ∙ E6')
  cellR = cong-tri rf0 e4 (cong fC eU3) e6

  Kap : EA ∙ (E2' ∙ EB) ≡ E4' ∙ (EC ∙ E6')
  Kap = sym cellL ∙ (cong (cong rf0) κ ∙ cellR)

  zig₁ : α ∙ (EA ∙ (E2' ∙ EB))
         ≡ (cong rfq K1 ∙ (KA2 zr1 ∙ cong rfs K3)) ∙ δ
  zig₁ = zig3 α β γ δ (cong rfq K1) (KA2 zr1) (cong rfs K3) EA E2' EB A1 A2 A3

  zig₂ : α ∙ (E4' ∙ (EC ∙ E6'))
         ≡ (KA4 zs1 ∙ (cong rfr K5 ∙ KA6 zq1)) ∙ δ
  zig₂ = zig3 α ε ζ δ (KA4 zs1) (cong rfr K5) (KA6 zq1) E4' EC E6' A4 A5 A6

  Ẽp : (cong rfq K1 ∙ (KA2 zr1 ∙ cong rfs K3)) ∙ δ
       ≡ (KA4 zs1 ∙ (cong rfr K5 ∙ KA6 zq1)) ∙ δ
  Ẽp = sym zig₁ ∙ (cong (α ∙_) Kap ∙ zig₂)

  -- the six reference edges
  αt : _
  αt = _⊙_ {P = S0}
           (sigT-map-eq {P = S1} {Q = S0} {f = rfq} Fq {p = cong rur pIs}
              (sigT-map-eq {P = S2} {Q = S1} {f = rur} Rr {p = pIs} (sym kP)))
           (_⊙_ {P = S0}
                (sigT-map-eq {P = S1} {Q = S0} {f = rfq} Fq {p = pV0}
                             (sym kbP))
                (sym kc0))

  βt : _
  βt = _⊙_ {P = S0}
           (sigT-map-eq {P = S1} {Q = S0} {f = rfq} Fq {p = cong rus pIr}
              (sigT-map-eq {P = S2} {Q = S1} {f = rus} Rs {p = pIr} (sym kQ)))
           (_⊙_ {P = S0}
                (sigT-map-eq {P = S1} {Q = S0} {f = rfq} Fq {p = pV1}
                             (sym kbQ))
                (sym kc1))

  γt : _
  γt = _⊙_ {P = S0}
           (sigT-map-eq {P = S1} {Q = S0} {f = rfs} Fs {p = cong ruq1 pIr}
              (sigT-map-eq {P = S2} {Q = S1} {f = ruq1} Rq1 {p = pIr}
                           (sym kQ)))
           (_⊙_ {P = S0}
                (sigT-map-eq {P = S1} {Q = S0} {f = rfs} Fs {p = pV2}
                             (sym kbR))
                (sym kc2))

  δt : _
  δt = _⊙_ {P = S0}
           (sigT-map-eq {P = S1} {Q = S0} {f = rfs} Fs {p = cong rur1 pIq}
              (sigT-map-eq {P = S2} {Q = S1} {f = rur1} Rr1 {p = pIq}
                           (sym kR)))
           (_⊙_ {P = S0}
                (sigT-map-eq {P = S1} {Q = S0} {f = rfs} Fs {p = pV3}
                             (sym kbR'))
                (sym kc3))

  εt : _
  εt = _⊙_ {P = S0}
           (sigT-map-eq {P = S1} {Q = S0} {f = rfr} Fr {p = cong ruq1 pIs}
              (sigT-map-eq {P = S2} {Q = S1} {f = ruq1} Rq1 {p = pIs}
                           (sym kP)))
           (_⊙_ {P = S0}
                (sigT-map-eq {P = S1} {Q = S0} {f = rfr} Fr {p = pV4}
                             (sym kbW))
                (sym kc4))

  ζt : _
  ζt = _⊙_ {P = S0}
           (sigT-map-eq {P = S1} {Q = S0} {f = rfr} Fr {p = cong rus pIq}
              (sigT-map-eq {P = S2} {Q = S1} {f = rus} Rs {p = pIq} (sym kR)))
           (_⊙_ {P = S0}
                (sigT-map-eq {P = S1} {Q = S0} {f = rfr} Fr {p = pV5}
                             (sym kbW'))
                (sym kc5))

  -- the inner hexagon's edges
  D1 : _
  D1 = sigT-map-eq {P = S1} {Q = S0} {f = rfq} Fq {p = K1} HK1

  D3 : _
  D3 = sigT-map-eq {P = S1} {Q = S0} {f = rfs} Fs {p = K3} HK3

  D5 : _
  D5 = sigT-map-eq {P = S1} {Q = S0} {f = rfr} Fr {p = K5} HK5

  -- the six fiber edges
  E1s : Sq S0 A1 (_⊙_ {P = S0} αt C1comp) (_⊙_ {P = S0} D1 βt)
  E1s = map-edge-Sq {S2 = S2} {S1 = S1} {S0 = S0} {rur = rur} {rus = rus}
          {uf0 = uf0} {rf = rfq} {rf0 = rf0} {fX = fA}
          Rr Rs Fq gq pIs pIr eU1 pV0 pV1 K1 HH1 a FIs FIr HK1
          aP kP aQ kQ bP kbP bQ kbQ cA0 kc0 cA1 kc1

  E2s : Sq S0 A2 (_⊙_ {P = S0} βt C2comp)
                 (_⊙_ {P = S0} (HKA2 zr1 (FIr a)) γt)
  E2s = k-edge-Sq {S2 = S2} {S1 = S1} {S0 = S0} {rus = rus} {ruq1 = ruq1}
          {rfq = rfq} {rfs = rfs} {rf0 = rf0} Fq Fs Rs Rq1 {KA = KA2} HKA2
          pIr kQ e2 pV1 pV2 (gq u1) (gs u2) HH2 bQ kbQ bR kbR cA1 kc1 cB2 kc2

  E3s : Sq S0 A3 (_⊙_ {P = S0} γt C3comp) (_⊙_ {P = S0} D3 δt)
  E3s = map-edge-Sq {S2 = S2} {S1 = S1} {S0 = S0} {rur = ruq1} {rus = rur1}
          {uf0 = uf0} {rf = rfs} {rf0 = rf0} {fX = fB}
          Rq1 Rr1 Fs gs pIr pIq eU2 pV2 pV3 K3 HH3 a FIr FIq HK3
          aQ kQ aR kR bR kbR bR' kbR' cB2 kc2 cB3 kc3

  E4s : Sq S0 A4 (_⊙_ {P = S0} αt C4comp)
                 (_⊙_ {P = S0} (HKA4 zs1 (FIs a)) εt)
  E4s = k-edge-Sq {S2 = S2} {S1 = S1} {S0 = S0} {rus = rur} {ruq1 = ruq1}
          {rfq = rfq} {rfs = rfr} {rf0 = rf0} Fq Fr Rr Rq1 {KA = KA4} HKA4
          pIs kP e4 pV0 pV4 (gq u0) (gr u4) HH4 bP kbP bW kbW cA0 kc0 cC4 kc4

  E5s : Sq S0 A5 (_⊙_ {P = S0} εt C5comp) (_⊙_ {P = S0} D5 ζt)
  E5s = map-edge-Sq {S2 = S2} {S1 = S1} {S0 = S0} {rur = ruq1} {rus = rus}
          {uf0 = uf0} {rf = rfr} {rf0 = rf0} {fX = fC}
          Rq1 Rs Fr gr pIs pIq eU3 pV4 pV5 K5 HH5 a FIs FIq HK5
          aP kP aR kR bW kbW bW' kbW' cC4 kc4 cC5 kc5

  E6s : Sq S0 A6 (_⊙_ {P = S0} ζt C6comp)
                 (_⊙_ {P = S0} (HKA6 zq1 (FIq a)) δt)
  E6s = k-edge-Sq {S2 = S2} {S1 = S1} {S0 = S0} {rus = rus} {ruq1 = rur1}
          {rfq = rfr} {rfs = rfs} {rf0 = rf0} Fr Fs Rs Rr1 {KA = KA6} HKA6
          pIq kR e6 pV5 pV3 (gr u5) (gs u3) HH6 bW' kbW' bR' kbR' cC5 kc5
          cB3 kc3

  -- the two triangles, Hcoh2Painting whiskered by δt, and the paste
  Z1 : Sq S0 zig₁ (_⊙_ {P = S0} αt (_⊙_ {P = S0} C1comp
                                        (_⊙_ {P = S0} C2comp C3comp)))
                  (_⊙_ {P = S0} (_⊙_ {P = S0} D1
                                      (_⊙_ {P = S0} (HKA2 zr1 (FIr a)) D3)) δt)
  Z1 = zig3-Sq S0 αt βt γt δt D1 (HKA2 zr1 (FIr a)) D3
                  C1comp C2comp C3comp E1s E2s E3s

  Z2 : Sq S0 zig₂ (_⊙_ {P = S0} αt (_⊙_ {P = S0} C4comp
                                        (_⊙_ {P = S0} C5comp C6comp)))
                  (_⊙_ {P = S0} (_⊙_ {P = S0} (HKA4 zs1 (FIs a))
                                      (_⊙_ {P = S0} D5 (HKA6 zq1 (FIq a))))
                       δt)
  Z2 = zig3-Sq S0 αt εt ζt δt (HKA4 zs1 (FIs a)) D5 (HKA6 zq1 (FIq a))
                  C4comp C5comp C6comp E4s E5s E6s

  HP : Sq S0 HHA (_⊙_ {P = S0} D1 (_⊙_ {P = S0} (HKA2 zr1 (FIr a)) D3))
                 (_⊙_ {P = S0} (HKA4 zs1 (FIs a))
                      (_⊙_ {P = S0} D5 (HKA6 zq1 (FIq a))))
  HP = subst→Sq S0 HHA Hcoh2Painting

  comp : Sq S0 (zig₁ ∙ (cong (_∙ δ) HHA ∙ sym zig₂))
           (_⊙_ {P = S0} αt (_⊙_ {P = S0} C1comp
                                 (_⊙_ {P = S0} C2comp C3comp)))
           (_⊙_ {P = S0} αt (_⊙_ {P = S0} C4comp
                                 (_⊙_ {P = S0} C5comp C6comp)))
  comp = Sq-∙ S0 Z1 (Sq-∙ S0 (⊙-whisker-l S0 δt HP) (Sq-sym S0 Z2))

  baseEq2 : zig₁ ∙ (cong (_∙ δ) HHA ∙ sym zig₂) ≡ cong (α ∙_) Kap
  baseEq2 =
      cong (λ h → zig₁ ∙ (cong (_∙ δ) h ∙ sym zig₂)) Hcoh3Frame
    ∙ cong (λ m → zig₁ ∙ (m ∙ sym zig₂)) (whisker-cancel δ Ẽp)
    ∙ cong (zig₁ ∙_)
           (∙-assoc (sym zig₁) (cong (α ∙_) Kap ∙ zig₂) (sym zig₂))
    ∙ ∙-cancel-l (sym zig₁) ((cong (α ∙_) Kap ∙ zig₂) ∙ sym zig₂)
    ∙ ∙-cancel-r (cong (α ∙_) Kap) zig₂

  core : Sq S0 Kap
           (_⊙_ {P = S0} C1comp (_⊙_ {P = S0} C2comp C3comp))
           (_⊙_ {P = S0} C4comp (_⊙_ {P = S0} C5comp C6comp))
  core = ⊙-cancel-r S0 αt (Sq-cast S0 baseEq2 comp)

  bridgeL : Sq S0 cellL
              (_⊙_ {P = S0r} C1comp (_⊙_ {P = S0r} C2comp C3comp))
              (_⊙_ {P = S0} C1comp (_⊙_ {P = S0} C2comp C3comp))
  bridgeL = Sq-∙ S0 (⊙-reindex S0 rf0 C1comp (_⊙_ {P = S0r} C2comp C3comp))
                    (⊙-whisker-r S0 C1comp (⊙-reindex S0 rf0 C2comp C3comp))

  bridgeR : Sq S0 cellR
              (_⊙_ {P = S0r} C4comp (_⊙_ {P = S0r} C5comp C6comp))
              (_⊙_ {P = S0} C4comp (_⊙_ {P = S0} C5comp C6comp))
  bridgeR = Sq-∙ S0 (⊙-reindex S0 rf0 C4comp (_⊙_ {P = S0r} C5comp C6comp))
                    (⊙-whisker-r S0 C4comp (⊙-reindex S0 rf0 C5comp C6comp))

  baseEq : cellL ∙ (Kap ∙ sym cellR) ≡ cong (cong rf0) κ
  baseEq =
      cong (cellL ∙_)
           (∙-assoc (sym cellL) (cong (cong rf0) κ ∙ cellR) (sym cellR))
    ∙ ∙-cancel-l (sym cellL) ((cong (cong rf0) κ ∙ cellR) ∙ sym cellR)
    ∙ ∙-cancel-r (cong (cong rf0) κ) cellR

  FINAL : Sq S0r κ
            (_⊙_ {P = S0r} C1comp (_⊙_ {P = S0r} C2comp C3comp))
            (_⊙_ {P = S0r} C4comp (_⊙_ {P = S0r} C5comp C6comp))
  FINAL = Sq-cast S0 baseEq
            (Sq-∙ S0 bridgeL (Sq-∙ S0 core (Sq-sym S0 bridgeR)))


------------------------------------------------------------------------
-- The Π-layer analogue of νGpd/Layer.v's Hexagon section
-- (lmap2_hex_rew_eq / layer_dpath2_eq / nth_dpath_*).
--
-- With layers as literal Π-types, a PathP between layers is a function
-- of PathPs *definitionally* (λ-exchange), so the Rocq layer-2-cell
-- extensionality (layer_dpath2_eq) shrinks to: conjugate the two
-- subst-form 2-cells through toPathP/fromPathP, exchange the ω-binder
-- with the two path binders, and convert back (Π-hex-bridge below).
--
-- The rest is the Πcomp-commutation suite (Rocq's nth_dpath_trans /
-- nth_dpath_sigT_map_eq / nth_dpath_lmap2_rew_eq): the ω-component of
-- each composite 2-cell factor is computed for ⊙ (Πcomp-⊙),
-- sigT-map-eq of a pointwise layer map (Πcomp-sigT-map-eq),
-- RewLemmas' Π-subst-ext (Πcomp-Π-subst-ext), plain right composition
-- (Πcomp-∙), transport along an index 2-cell (Πcomp-subst2),
-- cong-of-subst (Πcomp-cong-subst) and refl-index paths (Πcomp-refl),
-- with the Π-transport noise isolated in noiseΠ.  With these,
-- mkCoh2Layer's proof reduces to rew-coh2Layer above plus one GUIP
-- cell; see νGpd.agda's resume block.
------------------------------------------------------------------------

-- The ω-component of a Π-subst-equation (Rocq's nth_dpath).

Πcomp : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
        {t1 t2 : T} {e : t1 ≡ t2}
        {f : (ω : A') → B ω t1} {g : (ω : A') → B ω t2}
        (u : subst (λ t → (ω : A') → B ω t) e f ≡ g) (ω : A')
        → subst (B ω) e (f ω) ≡ g ω
Πcomp {A' = A'} {B = B} {e = e} {f = f} {g = g} u ω =
  fromPathP {P = λ i → B ω (e i)} {x = f ω} {y = g ω}
    (λ i → toPathP {P = λ i → (ω' : A') → B ω' (e i)} {x = f} {y = g} u i ω)

-- Inverse of toPathP-over above: recover the subst-form 2-cell
-- from a PathP square between the toPathP-images.

fromPathP-over : {A : Set ℓ} {Q : A → Set ℓ'} {x y : A}
  {p1 p2 : x ≡ y} (κ : p1 ≡ p2) {a : Q x} {b : Q y}
  (u : subst Q p1 a ≡ b) (v : subst Q p2 a ≡ b)
  (SQ : PathP (λ k → PathP (λ i → Q (κ k i)) a b)
              (toPathP {P = λ i → Q (p1 i)} u)
              (toPathP {P = λ i → Q (p2 i)} v))
  → subst (λ p → subst Q p a ≡ b) κ u ≡ v
fromPathP-over {Q = Q} {p1 = p1} κ {a} {b} u =
  J (λ p2 κ → (v : subst Q p2 a ≡ b)
              → PathP (λ k → PathP (λ i → Q (κ k i)) a b)
                      (toPathP {P = λ i → Q (p1 i)} u)
                      (toPathP {P = λ i → Q (κ i1 i)} v)
              → subst (λ p → subst Q p a ≡ b) κ u ≡ v)
    (λ v SQ → substRefl (λ p → subst Q p a ≡ b) u
              ∙ sym (fromPathP-toPathP (λ i → Q (p1 i)) u)
              ∙ cong (fromPathP {P = λ i → Q (p1 i)}) SQ
              ∙ fromPathP-toPathP (λ i → Q (p1 i)) v)
    κ

-- The hexagon transfer: a 2-cell between transported Π-valued
-- subst-equations follows from its ω-components (Rocq's
-- layer_dpath2_eq, with ext2 replaced by the definitional λ-exchange).

Π-hex-bridge :
  {A' : Set ℓ} {X : Set ℓ'} {B : A' → X → Set ℓ''}
  {x y : X} {e1 e2 : x ≡ y} (κ : e1 ≡ e2)
  {f : (ω : A') → B ω x} {g : (ω : A') → B ω y}
  (u : subst (λ x' → (ω : A') → B ω x') e1 f ≡ g)
  (v : subst (λ x' → (ω : A') → B ω x') e2 f ≡ g)
  (H : (ω : A') → subst (λ e → subst (B ω) e (f ω) ≡ g ω) κ
                    (Πcomp {B = B} {e = e1} {f = f} {g = g} u ω)
                  ≡ Πcomp {B = B} {e = e2} {f = f} {g = g} v ω)
  → subst (λ e → subst (λ x' → (ω : A') → B ω x') e f ≡ g) κ u ≡ v
Π-hex-bridge {A' = A'} {B = B} {x = x} {y = y} {e1 = e1} {e2 = e2} κ
             {f = f} {g = g} u v H =
  fromPathP-over {Q = λ x' → (ω : A') → B ω x'} κ u v
    (λ k i ω → sq' ω k i)
  where
  -- the toPathP-lines of u and v, and their ω-components
  ru : PathP (λ i → (ω : A') → B ω (e1 i)) f g
  ru = toPathP {P = λ i → (ω : A') → B ω (e1 i)} u
  rv : PathP (λ i → (ω : A') → B ω (e2 i)) f g
  rv = toPathP {P = λ i → (ω : A') → B ω (e2 i)} v

  cu : (ω : A') → subst (B ω) e1 (f ω) ≡ g ω
  cu ω = Πcomp {B = B} {e = e1} {f = f} {g = g} u ω
  cv : (ω : A') → subst (B ω) e2 (f ω) ≡ g ω
  cv ω = Πcomp {B = B} {e = e2} {f = f} {g = g} v ω

  -- the square over κ from the pointwise hypothesis
  sq : (ω : A') → PathP (λ k → PathP (λ i → B ω (κ k i)) (f ω) (g ω))
                        (toPathP {P = λ i → B ω (e1 i)} (cu ω))
                        (toPathP {P = λ i → B ω (e2 i)} (cv ω))
  sq ω = subst (λ z → PathP (λ k → PathP (λ i → B ω (κ k i)) (f ω) (g ω))
                            (toPathP {P = λ i → B ω (e1 i)} (cu ω)) z)
               (cong (toPathP {P = λ i → B ω (e2 i)}) (H ω))
               (toPathP-over {Q = B ω} κ (cu ω))

  -- endpoint corrections: toPathP (Πcomp u ω) is toPathP∘fromPathP of
  -- the ω-component line of u
  sq' : (ω : A') → PathP (λ k → PathP (λ i → B ω (κ k i)) (f ω) (g ω))
                         (λ i → ru i ω) (λ i → rv i ω)
  sq' ω =
    subst (λ z → PathP (λ k → PathP (λ i → B ω (κ k i)) (f ω) (g ω))
                       z (λ i → rv i ω))
          (toPathP-fromPathP (λ i → B ω (e1 i)) {x = f ω} {y = g ω}
            (λ i → ru i ω))
      (subst (λ z → PathP (λ k → PathP (λ i → B ω (κ k i)) (f ω) (g ω))
                          (toPathP {P = λ i → B ω (e1 i)} (cu ω)) z)
             (toPathP-fromPathP (λ i → B ω (e2 i)) {x = f ω} {y = g ω}
               (λ i → rv i ω))
             (sq ω))

------------------------------------------------------------------------
-- The Πcomp-commutation suite (Rocq's nth_dpath_* lemmas).
------------------------------------------------------------------------

-- The cubical assembly of a layer path from its components (the clean
-- counterpart of RewLemmas.Π-subst-ext; they agree, see below).

Π-ext' : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
         {t1 t2 : T} (e : t1 ≡ t2)
         {f : (ω : A') → B ω t1} {g : (ω : A') → B ω t2}
         (H : (ω : A') → subst (B ω) e (f ω) ≡ g ω)
         → subst (λ t → (ω : A') → B ω t) e f ≡ g
Π-ext' {A' = A'} {B = B} e {f} {g} H =
  fromPathP {P = λ i → (ω : A') → B ω (e i)} {x = f} {y = g}
    (λ i ω → toPathP {P = λ i → B ω (e i)} {x = f ω} {y = g ω} (H ω) i)

-- Πcomp is a retraction of Π-ext' (both round trips are the
-- toPathP/fromPathP ones).

Πcomp-Π-ext' : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} (e : t1 ≡ t2)
  {f : (ω : A') → B ω t1} {g : (ω : A') → B ω t2}
  (H : (ω : A') → subst (B ω) e (f ω) ≡ g ω) (ω : A')
  → Πcomp {B = B} {e = e} {f = f} {g = g} (Π-ext' {B = B} e {f = f} {g = g} H) ω ≡ H ω
Πcomp-Π-ext' {A' = A'} {B = B} e {f} {g} H ω =
  cong (λ (w : PathP (λ i → (ω' : A') → B ω' (e i)) f g)
          → fromPathP {P = λ i → B ω (e i)} {x = f ω} {y = g ω}
              (λ i → w i ω))
       (toPathP-fromPathP (λ i → (ω' : A') → B ω' (e i)) {x = f} {y = g}
         (λ i ω' → toPathP {P = λ i → B ω' (e i)} {x = f ω'} {y = g ω'}
                     (H ω') i))
  ∙ fromPathP-toPathP (λ i → B ω (e i)) {x = f ω} {y = g ω} (H ω)

-- RewLemmas' J-built Π-subst-ext agrees with Π-ext' (JRefl plus the
-- constant-line values of toPathP/fromPathP).

Π-subst-ext≡Π-ext' : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} (e : t1 ≡ t2)
  {f : (ω : A') → B ω t1} {g : (ω : A') → B ω t2}
  (H : (ω : A') → subst (B ω) e (f ω) ≡ g ω)
  → Π-subst-ext {B = B} e {f = f} {g = g} H ≡ Π-ext' {B = B} e {f = f} {g = g} H
Π-subst-ext≡Π-ext' {A' = A'} {T = T} {B = B} {t1 = t1} e {f} {g} H =
  J (λ t2 e → {g : (ω : A') → B ω t2}
              (H : (ω : A') → subst (B ω) e (f ω) ≡ g ω)
              → Π-subst-ext {B = B} e {f = f} {g = g} H
                ≡ Π-ext' {B = B} e {f = f} {g = g} H)
    (λ {g} H →
      cong (λ (F : {g : (ω : A') → B ω t1}
                   → ((ω : A') → subst (B ω) refl (f ω) ≡ g ω)
                   → subst (λ d → (ω : A') → B ω d) refl f ≡ g)
              → F {g = g} H)
           (JRefl (λ _ E1 → {g : _}
                            → ((ω : _) → subst (B ω) E1 (f ω) ≡ g ω)
                            → subst (λ d → (ω : _) → B ω d) E1 f ≡ g)
                  (λ {g} H → transportRefl f
                             ∙ funExt (λ ω → sym (transportRefl (f ω))
                                             ∙ H ω)))
      ∙ sym (cong (λ (h : (ω : A') → f ω ≡ g ω)
                     → transportRefl f ∙ funExt h)
                  (funExt (λ ω → toPathPConst {x = f ω} {y = g ω} (H ω))))
      ∙ sym (fromPathPConst {x = f} {y = g}
              (λ i ω → toPathP {P = λ _ → B ω t1}
                         {x = f ω} {y = g ω} (H ω) i)))
    e H

Πcomp-Π-subst-ext : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} (e : t1 ≡ t2)
  {f : (ω : A') → B ω t1} {g : (ω : A') → B ω t2}
  (H : (ω : A') → subst (B ω) e (f ω) ≡ g ω) (ω : A')
  → Πcomp {B = B} {e = e} {f = f} {g = g}
      (Π-subst-ext {B = B} e {f = f} {g = g} H) ω ≡ H ω
Πcomp-Π-subst-ext {B = B} {t1 = t1} {t2 = t2} e {f} {g} H ω =
  cong (λ u → Πcomp {B = B} {e = e} {f = f} {g = g} u ω)
       (Π-subst-ext≡Π-ext' {B = B} e {f = f} {g = g} H)
  ∙ Πcomp-Π-ext' {B = B} e {f = f} {g = g} H ω

-- Πcomp commutes with transporting along a 2-cell of index paths
-- (needed to push components through ⊙'s defining subst).

Πcomp-subst2 : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} {e e' : t1 ≡ t2} (S : e ≡ e')
  {f : (ω : A') → B ω t1} {g : (ω : A') → B ω t2}
  (M : subst (λ t → (ω' : A') → B ω' t) e f ≡ g) (ω : A')
  → Πcomp {B = B} {e = e'} {f = f} {g = g}
      (subst (λ e0 → subst (λ t → (ω' : A') → B ω' t) e0 f ≡ g) S M) ω
    ≡ subst (λ e0 → subst (B ω) e0 (f ω) ≡ g ω) S
        (Πcomp {B = B} {e = e} {f = f} {g = g} M ω)
Πcomp-subst2 {A' = A'} {B = B} {e = e} S {f = f} {g = g} M ω =
  J (λ e' S → Πcomp {B = B} {e = e'} {f = f} {g = g}
                (subst (λ e0 → subst (λ t → (ω' : A') → B ω' t) e0 f ≡ g)
                       S M) ω
              ≡ subst (λ e0 → subst (B ω) e0 (f ω) ≡ g ω) S
                  (Πcomp {B = B} {e = e} {f = f} {g = g} M ω))
    (cong (λ M' → Πcomp {B = B} {e = e} {f = f} {g = g} M' ω)
          (substRefl (λ e0 → subst (λ t → (ω' : A') → B ω' t) e0 f ≡ g) M)
     ∙ sym (substRefl (λ e0 → subst (B ω) e0 (f ω) ≡ g ω)
             (Πcomp {B = B} {e = e} {f = f} {g = g} M ω)))
    S

-- Πcomp past a fiberwise layer map (Rocq's nth_dpath_sigT_map_eq):
-- the Σ-map is pointwise, so both sides shrink to the same center by
-- one toPathP∘fromPathP round trip each.

Πcomp-sigT-map-eq :
  {ℓs ℓp : Level}
  {A' : Set ℓ} {T : Set ℓ'} {T' : Set ℓ''}
  {S : A' → T → Set ℓs} {P : A' → T' → Set ℓp}
  {fA : T → T'} (NA : (t : T) (ω : A') → S ω t → P ω (fA t))
  {d1 d2 : T} {p : d1 ≡ d2}
  {u : (ω : A') → S ω d1} {v : (ω : A') → S ω d2}
  (M : subst (λ t → (ω : A') → S ω t) p u ≡ v) (ω : A')
  → Πcomp {B = P} {e = cong fA p}
      {f = λ ω' → NA d1 ω' (u ω')} {g = λ ω' → NA d2 ω' (v ω')}
      (sigT-map-eq {P = λ t → (ω' : A') → S ω' t}
                   {Q = λ t' → (ω' : A') → P ω' t'} {f = fA}
                   (λ t ll ω' → NA t ω' (ll ω'))
                   {x = d1} {y = d2} {u = u} {v = v} {p = p} M) ω
    ≡ sigT-map-eq {P = S ω} {Q = P ω} {f = fA} (λ t x → NA t ω x)
        {x = d1} {y = d2} {u = u ω} {v = v ω} {p = p}
        (Πcomp {B = S} {e = p} {f = u} {g = v} M ω)
Πcomp-sigT-map-eq {A' = A'} {S = S} {P = P} {fA = fA} NA
                  {d1} {d2} {p} {u} {v} M ω =
  cong (λ (w : PathP (λ i → (ω' : A') → P ω' (fA (p i)))
                     (λ ω' → NA d1 ω' (u ω')) (λ ω' → NA d2 ω' (v ω')))
          → fromPathP {P = λ i → P ω (fA (p i))}
              {x = NA d1 ω (u ω)} {y = NA d2 ω (v ω)} (λ i → w i ω))
       (toPathP-fromPathP (λ i → (ω' : A') → P ω' (fA (p i)))
         {x = λ ω' → NA d1 ω' (u ω')} {y = λ ω' → NA d2 ω' (v ω')}
         (λ i ω' → NA (p i) ω'
            (toPathP {P = λ i → (ω'' : A') → S ω'' (p i)} {x = u} {y = v}
              M i ω')))
  ∙ sym (cong (λ (w : PathP (λ i → S ω (p i)) (u ω) (v ω))
                 → fromPathP {P = λ i → P ω (fA (p i))}
                     {x = NA d1 ω (u ω)} {y = NA d2 ω (v ω)}
                     (λ i → NA (p i) ω (w i)))
              (toPathP-fromPathP (λ i → S ω (p i)) {x = u ω} {y = v ω}
                (λ i → toPathP {P = λ i → (ω'' : A') → S ω'' (p i)}
                         {x = u} {y = v} M i ω)))

-- Πcomp past a right homogeneous composition factor.

Πcomp-∙ : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} {e : t1 ≡ t2}
  {f : (ω : A') → B ω t1} {g h : (ω : A') → B ω t2}
  (α : subst (λ t → (ω : A') → B ω t) e f ≡ g) (β : g ≡ h) (ω : A')
  → Πcomp {B = B} {e = e} {f = f} {g = h} (α ∙ β) ω
    ≡ Πcomp {B = B} {e = e} {f = f} {g = g} α ω ∙ funExt⁻ β ω
Πcomp-∙ {A' = A'} {B = B} {e = e} {f = f} {g = g} α β ω =
  J (λ h β → Πcomp {B = B} {e = e} {f = f} {g = h} (α ∙ β) ω
             ≡ Πcomp {B = B} {e = e} {f = f} {g = g} α ω ∙ funExt⁻ β ω)
    (cong (λ z → Πcomp {B = B} {e = e} {f = f} {g = g} z ω)
          (sym (rUnit α))
     ∙ rUnit (Πcomp {B = B} {e = e} {f = f} {g = g} α ω))
    β

-- The Π-transport noise path: applying a transported layer at ω versus
-- transporting the component.

noiseΠ : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} (e : t1 ≡ t2) (u : (ω : A') → B ω t1) (ω : A')
  → subst (λ t → (ω' : A') → B ω' t) e u ω ≡ subst (B ω) e (u ω)
noiseΠ {A' = A'} {B = B} e u ω =
  J (λ t2 e → subst (λ t → (ω' : A') → B ω' t) e u ω
              ≡ subst (B ω) e (u ω))
    (funExt⁻ (transportRefl u) ω ∙ sym (transportRefl (u ω)))
    e

-- noiseΠ computed at refl (JRefl unfolding).

noiseΠ-refl : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 : T} (u : (ω : A') → B ω t1) (ω : A')
  → noiseΠ {B = B} (refl {x = t1}) u ω
    ≡ funExt⁻ (transportRefl u) ω ∙ sym (transportRefl (u ω))
noiseΠ-refl {A' = A'} {T = T} {B = B} {t1 = t1} u ω =
  JRefl (λ t2 e → subst (λ t → (ω' : A') → B ω' t) e u ω
                  ≡ subst (B ω) e (u ω))
        (funExt⁻ (transportRefl u) ω ∙ sym (transportRefl (u ω)))

-- The ω-component of a layer path over a refl index: funExt⁻ up to the
-- noise conjugator.

Πcomp-refl : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 : T} {f g : (ω : A') → B ω t1}
  (X : subst (λ t → (ω : A') → B ω t) (refl {x = t1}) f ≡ g) (ω : A')
  → Πcomp {B = B} {e = refl} {f = f} {g = g} X ω
    ≡ sym (noiseΠ {B = B} refl f ω) ∙ funExt⁻ X ω
Πcomp-refl {A' = A'} {B = B} {t1 = t1} {f = f} {g = g} X ω =
  fromPathPConst {x = f ω} {y = g ω}
    (λ i → toPathP {P = λ _ → (ω' : A') → B ω' t1} {x = f} {y = g} X i ω)
  ∙ cong (λ (w : f ≡ g) → transportRefl (f ω) ∙ funExt⁻ w ω)
         (toPathPConst {x = f} {y = g} X)
  ∙ sym (∙-assoc (transportRefl (f ω))
                 (sym (funExt⁻ (transportRefl f) ω)) (funExt⁻ X ω))
  ∙ cong (_∙ funExt⁻ X ω)
      (sym (cong sym (noiseΠ-refl {B = B} f ω)
            ∙ symDistr (funExt⁻ (transportRefl f) ω)
                       (sym (transportRefl (f ω)))))

-- The ω-component of a cong-of-subst along an index 2-cell.

Πcomp-cong-subst : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} {e1 e2 : t1 ≡ t2} (γ : e1 ≡ e2)
  (u : (ω : A') → B ω t1) (ω : A')
  → Πcomp {B = B} {e = e1} {f = u}
      {g = subst (λ t → (ω' : A') → B ω' t) e2 u}
      (cong (λ e → subst (λ t → (ω' : A') → B ω' t) e u) γ) ω
    ≡ cong (λ e → subst (B ω) e (u ω)) γ ∙ sym (noiseΠ {B = B} e2 u ω)
Πcomp-cong-subst {A' = A'} {T = T} {B = B} {t1 = t1} {t2 = t2} {e1 = e1} γ u ω =
  J (λ e2 γ → Πcomp {B = B} {e = e1} {f = u}
                {g = subst (λ t → (ω' : A') → B ω' t) e2 u}
                (cong (λ e → subst (λ t → (ω' : A') → B ω' t) e u) γ) ω
              ≡ cong (λ e → subst (B ω) e (u ω)) γ
                ∙ sym (noiseΠ {B = B} e2 u ω))
    (baseE t2 e1)
    γ
  where
  baseE : (t2' : T) (e : t1 ≡ t2')
          → Πcomp {B = B} {e = e} {f = u}
              {g = subst (λ t → (ω' : A') → B ω' t) e u}
              (refl {x = subst (λ t → (ω' : A') → B ω' t) e u}) ω
            ≡ refl ∙ sym (noiseΠ {B = B} e u ω)
  baseE t2' e =
    J (λ t2' e → Πcomp {B = B} {e = e} {f = u}
                  {g = subst (λ t → (ω' : A') → B ω' t) e u}
                  (refl {x = subst (λ t → (ω' : A') → B ω' t) e u}) ω
                ≡ refl ∙ sym (noiseΠ {B = B} e u ω))
      ( Πcomp-refl {B = B}
          {f = u} {g = subst (λ t → (ω' : A') → B ω' t) refl u}
          (refl {x = subst (λ t → (ω' : A') → B ω' t) refl u}) ω
        ∙ sym (rUnit (sym (noiseΠ {B = B} refl u ω)))
        ∙ lUnit (sym (noiseΠ {B = B} refl u ω)) )
      e


-- Groupoid mini-kit for the telescopes below.

conj-cancelL : {A : Set ℓ} {x y z : A} (n : x ≡ y) (a : y ≡ z)
               → sym n ∙ (n ∙ a) ≡ a
conj-cancelL n a =
  sym (∙-assoc (sym n) n a) ∙ cong (_∙ a) (lCancel n) ∙ sym (lUnit a)

∙-cong : {A : Set ℓ} {x y z : A} {a a' : x ≡ y} {b b' : y ≡ z}
         → a ≡ a' → b ≡ b' → a ∙ b ≡ a' ∙ b'
∙-cong α β = cong₂ _∙_ α β

-- funExt⁻ of a layer path over refl, unconjugated (inverse reading of
-- Πcomp-refl).

Πcomp-unconj : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 : T} {f g : (ω : A') → B ω t1}
  (X : subst (λ t → (ω : A') → B ω t) (refl {x = t1}) f ≡ g) (ω : A')
  → funExt⁻ {f = subst (λ t → (ω' : A') → B ω' t) refl f} {g = g} X ω
    ≡ noiseΠ {B = B} refl f ω ∙ Πcomp {B = B} {e = refl} {f = f} {g = g} X ω
Πcomp-unconj {A' = A'} {B = B} {t1 = t1} {f = f} {g = g} X ω =
  lUnit fX
  ∙ cong (_∙ fX) (sym (rCancel (noiseΠ {B = B} refl f ω)))
  ∙ ∙-assoc (noiseΠ {B = B} refl f ω) (sym (noiseΠ {B = B} refl f ω)) fX
  ∙ cong (noiseΠ {B = B} refl f ω ∙_)
         (sym (Πcomp-refl {B = B} {f = f} {g = g} X ω))
  where
  fX : subst (λ t → (ω' : A') → B ω' t) refl f ω ≡ g ω
  fX = funExt⁻ {f = subst (λ t → (ω' : A') → B ω' t) refl f} {g = g} X ω

-- Πcomp past ⊙ (Rocq's nth_dpath_trans): the index 2-cells of the two
-- ⊙'s agree definitionally (fst of a Σ-hcomp computes componentwise),
-- so after sigT-trans-eq-refl on both sides only the noiseΠ
-- conjugators remain, and they telescope away.

Πcomp-⊙ : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {x y z : T} {p : x ≡ y} {p' : y ≡ z}
  {u : (ω : A') → B ω x} {v : (ω : A') → B ω y} {w : (ω : A') → B ω z}
  (X : subst (λ t → (ω : A') → B ω t) p u ≡ v)
  (Y : subst (λ t → (ω : A') → B ω t) p' v ≡ w)
  (ω : A')
  → Πcomp {B = B} {e = p ∙ p'} {f = u} {g = w}
      (_⊙_ {P = λ t → (ω' : A') → B ω' t} {u = u} {v = v} {w = w}
           {p = p} X {p' = p'} Y) ω
    ≡ _⊙_ {P = B ω} {u = u ω} {v = v ω} {w = w ω}
        {p = p} (Πcomp {B = B} {e = p} {f = u} {g = v} X ω)
        {p' = p'} (Πcomp {B = B} {e = p'} {f = v} {g = w} Y ω)
Πcomp-⊙ {A' = A'} {T = T} {B = B} {x = x} {y = y} {z = z} {p = p}
        {p' = p'} {u = u} {v = v} {w = w} X Y ω =
  J (λ y p → (v : (ω' : A') → B ω' y)
             (X : subst (λ t → (ω' : A') → B ω' t) p u ≡ v)
             (z : T) (p' : y ≡ z) (w : (ω' : A') → B ω' z)
             (Y : subst (λ t → (ω' : A') → B ω' t) p' v ≡ w)
             → Πcomp {B = B} {e = p ∙ p'} {f = u} {g = w}
                 (_⊙_ {P = λ t → (ω' : A') → B ω' t} {u = u} {v = v}
                      {w = w} {p = p} X {p' = p'} Y) ω
               ≡ _⊙_ {P = B ω} {u = u ω} {v = v ω} {w = w ω}
                   {p = p} (Πcomp {B = B} {e = p} {f = u} {g = v} X ω)
                   {p' = p'} (Πcomp {B = B} {e = p'} {f = v} {g = w} Y ω))
    (λ v X z p' w Y →
      J (λ z p' → (w : (ω' : A') → B ω' z)
                  (Y : subst (λ t → (ω' : A') → B ω' t) p' v ≡ w)
                  → Πcomp {B = B} {e = refl ∙ p'} {f = u} {g = w}
                      (_⊙_ {P = λ t → (ω' : A') → B ω' t} {u = u} {v = v}
                           {w = w} {p = refl} X {p' = p'} Y) ω
                    ≡ _⊙_ {P = B ω} {u = u ω} {v = v ω} {w = w ω}
                        {p = refl}
                        (Πcomp {B = B} {e = refl} {f = u} {g = v} X ω)
                        {p' = p'}
                        (Πcomp {B = B} {e = p'} {f = v} {g = w} Y ω))
        (λ w Y → base v X w Y)
        p' w Y)
    p v X z p' w Y
  where
  L : T → Set _
  L t = (ω' : A') → B ω' t

  base : (v : (ω' : A') → B ω' x)
         (X : subst L (refl {x = x}) u ≡ v)
         (w : (ω' : A') → B ω' x)
         (Y : subst L (refl {x = x}) v ≡ w)
         → Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = w}
             (_⊙_ {P = L} {u = u} {v = v} {w = w}
                  {p = refl} X {p' = refl} Y) ω
           ≡ _⊙_ {P = B ω} {u = u ω} {v = v ω} {w = w ω}
               {p = refl} (Πcomp {B = B} {e = refl} {f = u} {g = v} X ω)
               {p' = refl} (Πcomp {B = B} {e = refl} {f = v} {g = w} Y ω)
  base v X w Y = b1 ∙ b2 ∙ b3 ∙ tele ∙ b5
    where
    nU nV : _
    nU = noiseΠ {B = B} refl u ω
    nV = noiseΠ {B = B} refl v ω
    N1v : subst L refl v ω ≡ v ω
    N1v = funExt⁻ (transportRefl v) ω
    N2v : subst (B ω) refl (v ω) ≡ v ω
    N2v = transportRefl (v ω)
    ΠcX = Πcomp {B = B} {e = refl} {f = u} {g = v} X ω
    ΠcY = Πcomp {B = B} {e = refl} {f = v} {g = w} Y ω
    cL : subst L (refl ∙ refl) u ≡ subst L refl u
    cL = cong (λ e → subst L e u)
              (sym (rUnit refl))
    cB : subst (B ω) (refl ∙ refl) (u ω) ≡ subst (B ω) refl (u ω)
    cB = cong (λ e → subst (B ω) e (u ω))
              (sym (rUnit refl))
    RST : subst L refl u ≡ w
    RST = X ∙ sym (substRefl L v) ∙ Y

    b1 : Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = w}
           (_⊙_ {P = L} {u = u} {v = v} {w = w}
                {p = refl} X {p' = refl} Y) ω
         ≡ Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = w} (cL ∙ RST) ω
    b1 = cong (λ q → Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = w} q ω)
              (sigT-trans-eq-refl {P = L} {u = u} {v = v} {w = w} X Y)

    b2 : Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = w} (cL ∙ RST) ω
         ≡ Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = subst L refl u}
             cL ω
           ∙ funExt⁻ RST ω
    b2 = Πcomp-∙ {B = B} {e = refl ∙ refl} {f = u}
           {g = subst L refl u} {h = w} cL RST ω

    id1 : Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = subst L refl u}
            cL ω
          ≡ cB ∙ sym nU
    id1 = Πcomp-cong-subst {B = B}
            (sym (rUnit refl)) u ω

    id2 : funExt⁻ X ω ≡ nU ∙ ΠcX
    id2 = Πcomp-unconj {B = B} {f = u} {g = v} X ω

    id3 : funExt⁻ {B = λ ω' → B ω' x} {f = v} {g = subst L refl v}
            (sym (substRefl L v)) ω
          ≡ sym N2v ∙ sym nV
    id3 = sym (cong (sym N2v ∙_)
                    (cong sym (noiseΠ-refl {B = B} v ω)
                     ∙ symDistr N1v (sym N2v))
               ∙ conj-cancelL N2v (sym N1v))

    id4 : funExt⁻ Y ω ≡ nV ∙ ΠcY
    id4 = Πcomp-unconj {B = B} {f = v} {g = w} Y ω

    b3 : Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = subst L refl u}
           cL ω
         ∙ funExt⁻ RST ω
         ≡ (cB ∙ sym nU)
           ∙ ((nU ∙ ΠcX) ∙ ((sym N2v ∙ sym nV) ∙ (nV ∙ ΠcY)))
    b3 = ∙-cong {x = subst (B ω) (refl ∙ refl) (u ω)}
           {y = subst L refl u ω} {z = w ω}
           id1
           (∙-cong {x = subst L refl u ω} {y = v ω} {z = w ω}
             id2
             (∙-cong {x = v ω} {y = subst L refl v ω} {z = w ω}
               id3 id4))

    tele : (cB ∙ sym nU)
           ∙ ((nU ∙ ΠcX) ∙ ((sym N2v ∙ sym nV) ∙ (nV ∙ ΠcY)))
           ≡ cB ∙ (ΠcX ∙ (sym N2v ∙ ΠcY))
    tele =
      cong (λ C' → (cB ∙ sym nU) ∙ ((nU ∙ ΠcX) ∙ C'))
           (∙-assoc (sym N2v) (sym nV) (nV ∙ ΠcY)
            ∙ cong (sym N2v ∙_) (conj-cancelL nV ΠcY))
      ∙ cong ((cB ∙ sym nU) ∙_)
             (∙-assoc nU ΠcX (sym N2v ∙ ΠcY))
      ∙ ∙-assoc cB (sym nU) (nU ∙ (ΠcX ∙ (sym N2v ∙ ΠcY)))
      ∙ cong (cB ∙_) (conj-cancelL nU (ΠcX ∙ (sym N2v ∙ ΠcY)))

    b5 : cB ∙ (ΠcX ∙ (sym N2v ∙ ΠcY))
         ≡ _⊙_ {P = B ω} {u = u ω} {v = v ω} {w = w ω}
             {p = refl} ΠcX {p' = refl} ΠcY
    b5 = sym (sigT-trans-eq-refl {P = B ω} {u = u ω} {v = v ω} {w = w ω}
               ΠcX ΠcY)
