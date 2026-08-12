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
-- point is plain transport algebra.  (2) For destruct-heavy Rocq
-- proofs: the private inductive-Id kit at the end of the file, whose
-- reflId matches replay Rocq's destructs with definitional reduction.
--
-- rew_coh2Painting_restr0 and rew_coh2Layer are so far ported as
-- typechecked STATEMENTS only (…-Type definitions at the end of the
-- file); see the NOTEs there for what their proofs still need.
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

  --------------------------------------------------------------------
  -- The permutahedron replay at the Id level.  perm2ᴵ and perm1ᴵ are
  -- the two generalize blocks of the Rocq proof of
  -- permutahedral_coherence (νGpd/Lemmas.v); permᴵ is the full
  -- Id-level statement, whose six initial destructs happen before the
  -- generalization.  Every Rocq destruct is a reflId match, and the
  -- eq_trans/f_equal reductions Rocq's cbn performs hold
  -- definitionally for transId/congId (which match on their second
  -- resp. only Id argument, like Rocq's eq_trans/f_equal).
  --------------------------------------------------------------------

  -- Innermost stage: all points are variables; the remaining destructs
  -- (gq0, gs0, ge, then the k's forced via HH2/HH4/HH6) go through.
  perm2ᴵ : {X0 : Set ℓ} {x1 x2 x3 y : X0}
    (gq0 : Id x1 y) (gs0 : Id x2 y) (ge : Id x3 y)
    (k2 : Id x1 x2) (k4 : Id x1 x3) (k6 : Id x3 x2)
    (HH2 : Id (transId reflId gq0) (transId k2 (transId reflId gs0)))
    (HH4 : Id (transId reflId gq0) (transId k4 (transId reflId ge)))
    (HH6 : Id (transId reflId ge) (transId k6 (transId reflId gs0)))
    → Id (transId reflId k2) (transId k4 (transId reflId k6))
  perm2ᴵ reflId reflId reflId _ _ _ reflId reflId reflId = reflId

  -- Middle stage: the X1- and T-points are variables; the maps
  -- rfq/rfs/rfr/rf0 are still live (they appear in the conclusion).
  perm1ᴵ : {X1 : Set ℓ} {X0 : Set ℓ'} {T : Set ℓ''}
    (rfq rfs rfr : X1 → X0) (rf0 : T → X0)
    {w0 w1 w2 w3 w4 w5 V0 V2 V4 : X1} {TA TB TC : T}
    (pV0 : Id w0 V0) (pV1 : Id w1 V0)
    (pV2 : Id w2 V2) (pV3 : Id w3 V2)
    (pV4 : Id w4 V4) (pV5 : Id w5 V4)
    (K1 : Id w0 w1) (K3 : Id w2 w3) (K5 : Id w4 w5)
    (gq0 : Id (rfq V0) (rf0 TA)) (gs0 : Id (rfs V2) (rf0 TB))
    (ge : Id (rfr V4) (rf0 TC))
    (k2 : Id (rfq w1) (rfs w2)) (k4 : Id (rfq w0) (rfr w4))
    (k6 : Id (rfr w5) (rfs w3))
    (e2 : Id TA TB) (e4 : Id TA TC) (e6 : Id TC TB)
    (HH1 : Id (transId reflId pV0) (transId K1 (transId reflId pV1)))
    (HH3 : Id (transId reflId pV2) (transId K3 (transId reflId pV3)))
    (HH5 : Id (transId reflId pV4) (transId K5 (transId reflId pV5)))
    (HH2 : Id (transId (congId rfq pV1) (transId gq0 (congId rf0 e2)))
              (transId k2 (transId (congId rfs pV2) gs0)))
    (HH4 : Id (transId (congId rfq pV0) (transId gq0 (congId rf0 e4)))
              (transId k4 (transId (congId rfr pV4) ge)))
    (HH6 : Id (transId (congId rfr pV5) (transId ge (congId rf0 e6)))
              (transId k6 (transId (congId rfs pV3) gs0)))
    (κ : Id (transId reflId e2) (transId e4 (transId reflId e6)))
    → Id (transId (congId rfq K1) (transId k2 (congId rfs K3)))
         (transId k4 (transId (congId rfr K5) k6))
  perm1ᴵ rfq rfs rfr rf0
         reflId reflId reflId reflId reflId reflId
         _ _ _ gq0 gs0 ge k2 k4 k6 reflId _ reflId
         reflId reflId reflId HH2 HH4 HH6 reflId =
    perm2ᴵ gq0 gs0 ge k2 k4 k6 HH2 HH4 HH6

  -- Full Id-level permutahedral coherence, mirroring the Rocq
  -- statement 1:1 (with every eq replaced by Id).
  permᴵ : {X2 : Set ℓ} {X1 : Set ℓ'} {X0 : Set ℓ''}
    {TU : Set ℓ'''} {T : Set ℓp}
    (uf0 : TU → X1) (rf0 : T → X0) (fA fB fC : TU → T)
    (rfq rfs rfr : X1 → X0)
    (gq : (dd : TU) → Id (rfq (uf0 dd)) (rf0 (fA dd)))
    (gs : (dd : TU) → Id (rfs (uf0 dd)) (rf0 (fB dd)))
    (gr : (dd : TU) → Id (rfr (uf0 dd)) (rf0 (fC dd)))
    (rur rus ruq1 rur1 : X2 → X1)
    (KA2 : (z : X2) → Id (rfq (rus z)) (rfs (ruq1 z)))
    (KA4 : (z : X2) → Id (rfq (rur z)) (rfr (ruq1 z)))
    (KA6 : (z : X2) → Id (rfr (rus z)) (rfs (rur1 z)))
    (u0 u1 u2 u3 u4 u5 : TU)
    (eU1 : Id u0 u1) (eU2 : Id u2 u3) (eU3 : Id u4 u5)
    (e2 : Id (fA u1) (fB u2)) (e4 : Id (fA u0) (fC u4))
    (e6 : Id (fC u5) (fB u3))
    (zs1 zs2 zr1 zr2 zq1 zq2 : X2)
    (pIs : Id zs1 zs2) (pIr : Id zr1 zr2) (pIq : Id zq1 zq2)
    (pV0 : Id (rur zs2) (uf0 u0)) (pV1 : Id (rus zr2) (uf0 u1))
    (pV2 : Id (ruq1 zr2) (uf0 u2)) (pV3 : Id (rur1 zq2) (uf0 u3))
    (pV4 : Id (ruq1 zs2) (uf0 u4)) (pV5 : Id (rus zq2) (uf0 u5))
    (K1 : Id (rur zs1) (rus zr1)) (K3 : Id (ruq1 zr1) (rur1 zq1))
    (K5 : Id (ruq1 zs1) (rus zq1))
    (HH1 : Id (transId (congId rur pIs) (transId pV0 (congId uf0 eU1)))
              (transId K1 (transId (congId rus pIr) pV1)))
    (HH3 : Id (transId (congId ruq1 pIr) (transId pV2 (congId uf0 eU2)))
              (transId K3 (transId (congId rur1 pIq) pV3)))
    (HH5 : Id (transId (congId ruq1 pIs) (transId pV4 (congId uf0 eU3)))
              (transId K5 (transId (congId rus pIq) pV5)))
    (HH2 : Id (transId (congId rfq pV1) (transId (gq u1) (congId rf0 e2)))
              (transId (KA2 zr2) (transId (congId rfs pV2) (gs u2))))
    (HH4 : Id (transId (congId rfq pV0) (transId (gq u0) (congId rf0 e4)))
              (transId (KA4 zs2) (transId (congId rfr pV4) (gr u4))))
    (HH6 : Id (transId (congId rfr pV5) (transId (gr u5) (congId rf0 e6)))
              (transId (KA6 zq2) (transId (congId rfs pV3) (gs u3))))
    (κ : Id (transId (congId fA eU1) (transId e2 (congId fB eU2)))
            (transId e4 (transId (congId fC eU3) e6)))
    → Id (transId (congId rfq K1) (transId (KA2 zr1) (congId rfs K3)))
         (transId (KA4 zs1) (transId (congId rfr K5) (KA6 zq1)))
  permᴵ uf0 rf0 fA fB fC rfq rfs rfr gq gs gr rur rus ruq1 rur1
        KA2 KA4 KA6 u0 u1 u2 u3 u4 u5 reflId reflId reflId e2 e4 e6
        zs1 zs2 zr1 zr2 zq1 zq2 reflId reflId reflId
        pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5 HH1 HH3 HH5 HH2 HH4 HH6 κ =
    perm1ᴵ rfq rfs rfr rf0 pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5
           (gq u0) (gs u2) (gr u4) (KA2 zr1) (KA4 zs1) (KA6 zq1)
           e2 e4 e6 HH1 HH3 HH5 HH2 HH4 HH6 κ

------------------------------------------------------------------------
-- The permutahedral coherence of frames (νGpd/Lemmas.v):
-- the hexagon proved as a composition of the seven other hexagons of
-- the permutahedron.  Statement mirrors Rocq 1:1 (section context as
-- implicit arguments); the proof converts every hypothesis hexagon to
-- the Id level with hexToId, replays the Rocq destruct chain there
-- (permᴵ), and converts the resulting hexagon back with hexFromId.
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
  hexFromId (cong rfq K1) (KA2 zr1) (cong rfs K3)
            (KA4 zs1) (cong rfr K5) (KA6 zq1)
            (pathToId-cong rfq K1) refl (pathToId-cong rfs K3)
            refl (pathToId-cong rfr K5) refl
    (permᴵ uf0 rf0 fA fB fC rfq rfs rfr
           (λ dd → pathToId (gq dd)) (λ dd → pathToId (gs dd))
           (λ dd → pathToId (gr dd))
           rur rus ruq1 rur1
           (λ z → pathToId (KA2 z)) (λ z → pathToId (KA4 z))
           (λ z → pathToId (KA6 z))
           u0 u1 u2 u3 u4 u5
           (pathToId eU1) (pathToId eU2) (pathToId eU3)
           (pathToId e2) (pathToId e4) (pathToId e6)
           zs1 zs2 zr1 zr2 zq1 zq2
           (pathToId pIs) (pathToId pIr) (pathToId pIq)
           (pathToId pV0) (pathToId pV1) (pathToId pV2)
           (pathToId pV3) (pathToId pV4) (pathToId pV5)
           (pathToId K1) (pathToId K3) (pathToId K5)
           (hexToId (cong rur pIs) pV0 (cong uf0 eU1)
                    K1 (cong rus pIr) pV1
                    (pathToId-cong rur pIs) refl (pathToId-cong uf0 eU1)
                    refl (pathToId-cong rus pIr) refl HH1)
           (hexToId (cong ruq1 pIr) pV2 (cong uf0 eU2)
                    K3 (cong rur1 pIq) pV3
                    (pathToId-cong ruq1 pIr) refl (pathToId-cong uf0 eU2)
                    refl (pathToId-cong rur1 pIq) refl HH3)
           (hexToId (cong ruq1 pIs) pV4 (cong uf0 eU3)
                    K5 (cong rus pIq) pV5
                    (pathToId-cong ruq1 pIs) refl (pathToId-cong uf0 eU3)
                    refl (pathToId-cong rus pIq) refl HH5)
           (hexToId (cong rfq pV1) (gq u1) (cong rf0 e2)
                    (KA2 zr2) (cong rfs pV2) (gs u2)
                    (pathToId-cong rfq pV1) refl (pathToId-cong rf0 e2)
                    refl (pathToId-cong rfs pV2) refl HH2)
           (hexToId (cong rfq pV0) (gq u0) (cong rf0 e4)
                    (KA4 zs2) (cong rfr pV4) (gr u4)
                    (pathToId-cong rfq pV0) refl (pathToId-cong rf0 e4)
                    refl (pathToId-cong rfr pV4) refl HH4)
           (hexToId (cong rfr pV5) (gr u5) (cong rf0 e6)
                    (KA6 zq2) (cong rfs pV3) (gs u3)
                    (pathToId-cong rfr pV5) refl (pathToId-cong rf0 e6)
                    refl (pathToId-cong rfs pV3) refl HH6)
           (hexToId (cong fA eU1) e2 (cong fB eU2)
                    e4 (cong fC eU3) e6
                    (pathToId-cong fA eU1) refl (pathToId-cong fB eU2)
                    refl (pathToId-cong fC eU3) refl κ))

------------------------------------------------------------------------
-- rew_coh2Painting_restr0 (νGpd/Lemmas.v:449-494): statement, ported
-- 1:1 as a typechecked Set-valued definition.
--
-- NOTE (unfinished): the proof is not yet ported.  The Rocq proof is
-- subst kF kG kM kM'; destruct E1 e2 e5; generalize (r0 d1); destruct
-- pR; destruct κ (after cbn), HK; generalize (rr n1); destruct pQ;
-- reflexivity.  Its cubical replay needs, at the collapsed point, the
-- propositional values of rew-cohLayer33's constituents at refl
-- arguments (substCommSlice-refl and a naturality of substComposite in
-- its second path argument, since substComposite P p (refl ∙ refl) u
-- is not JRefl-extractable directly), plus a conjugation of κ by
-- lUnit/rUnit corrections so that it becomes J-eliminable against KA.
-- The J-cascade itself is routine given those pieces (same pattern as
-- ⊙-Σ≡dep/HexT above).
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
-- NOTE (unfinished): the proof is not yet ported.  The Rocq proof
-- (subst; destruct the twelve index paths; two generalize blocks;
-- sigT_map_eq_refl and sigT_trans_eq_refl rewrites; rewrite
-- Hcoh3Frame into Hcoh2Painting; final eq_trans_refl_l cleanups)
-- needs, beyond the restr0 prerequisites listed above, the collapsed
-- value of permutahedral-coherence (computable through hexToId/permᴵ/
-- hexFromId since permᴵ reduces definitionally on reflId), and the
-- same κ/HHA conjugation cascade.  All J-cascade patterns are already
-- exercised by ⊙-Σ≡dep and HexT above.
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
