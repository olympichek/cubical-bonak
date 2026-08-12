------------------------------------------------------------------------
-- Bonak.RewLemmas — transport lemmas mirroring Rocq's RewLemmas.v and
-- the Σ-path kit of SigT.v.
--
-- In cubical, `eq_existT_curried` and friends are PathP-pairings plus
-- the toPathP/fromPathP converters; `rew_cohLayer33` keeps its Rocq
-- statement (subst-form) and is proved by a substComposite /
-- substCommSlice chain.
------------------------------------------------------------------------

module Bonak.RewLemmas where

open import Bonak.Prelude

private variable
  ℓ ℓ' ℓ'' : Level
  A B : Set ℓ

-- Path induction (computes only propositionally in cubical — fine for
-- the propositional lemmas below, mirroring Rocq's destructs).
J : {x : A} (P : (y : A) → x ≡ y → Set ℓ') (d : P x refl)
    {y : A} (p : x ≡ y) → P y p
J P d p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

-- Path algebra ------------------------------------------------------------

compPath-filler : {x y z : A} (p : x ≡ y) (q : y ≡ z)
                  → PathP (λ j → x ≡ q j) p (p ∙ q)
compPath-filler {x = x} p q j i =
  hfill (λ k → λ { (i = i0) → x ; (i = i1) → q k }) (inS (p i)) j

rUnit : {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
rUnit p = compPath-filler p refl

∙-assoc : {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
          → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙-assoc p q r =
  J (λ _ r → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r))
    (sym (rUnit (p ∙ q)) ∙ cong (p ∙_) (rUnit q))
    r

-- subst lemmas -------------------------------------------------------------

substComposite : (P : A → Set ℓ') {x y z : A} (p : x ≡ y) (q : y ≡ z)
                 (u : P x) → subst P (p ∙ q) u ≡ subst P q (subst P p u)
substComposite P p q u =
  J (λ _ q → subst P (p ∙ q) u ≡ subst P q (subst P p u))
    (cong (λ e → subst P e u) (sym (rUnit p))
      ∙ sym (substRefl P (subst P p u)))
    q

-- Rocq's map_subst: transporting past a fiberwise function.
substCommSlice : {S : A → Set ℓ'} {P : B → Set ℓ''} (rf : A → B)
                 (φ : (a : A) → S a → P (rf a))
                 {m1 m2 : A} (p : m1 ≡ m2) (s : S m1)
                 → subst P (cong rf p) (φ m1 s) ≡ φ m2 (subst S p s)
substCommSlice {S = S} {P} rf φ p s =
  J (λ _ p → subst P (cong rf p) (φ _ s) ≡ φ _ (subst S p s))
    (substRefl P (φ _ s) ∙ cong (φ _) (sym (substRefl S s)))
    p

-- Σ-path kit (SigT.v) -------------------------------------------------------

-- eq_existT_curried: a Σ-path from a base path and a subst-equation.
Σ≡ : {P : A → Set ℓ'} {u1 v1 : A} {u2 : P u1} {v2 : P v1}
     (p : u1 ≡ v1) (q : subst P p u2 ≡ v2)
     → PathP (λ _ → Σ A P) (u1 , u2) (v1 , v2)
Σ≡ {P = P} p q i = p i , toPathP {P = λ i → P (p i)} q i

-- eq_existT_curried_dep: transporting a dependent pair along a base
-- path, componentwise.
Σ≡dep : {P : A → Set ℓ'} {Q : Σ A P → Set ℓ''}
        {x y : A} (H : x ≡ y)
        {u : P x} {v : Q (x , u)} {u' : P y} {v' : Q (y , u')}
        (Hu : subst P H u ≡ u') (Hv : subst Q (Σ≡ H Hu) v ≡ v')
        → subst (λ x → Σ (P x) (λ a → Q (x , a))) H (u , v) ≡ (u' , v')
Σ≡dep {P = P} {Q} H {u} {v} {u'} {v'} Hu Hv =
  fromPathP (λ i → hu i , hv i)
  where
  hu : PathP (λ i → P (H i)) u u'
  hu = toPathP {P = λ i → P (H i)} Hu
  hv : PathP (λ i → Q (H i , hu i)) v v'
  hv = toPathP {P = λ i → Q (H i , hu i)} Hv

-- The fused layer-coherence lemma (rew_cohLayer33) ---------------------------
--
-- Closes a layer coherence goal in one step: two transport chains, 3 on
-- the left and 3 on the right, whose starting elements are identified
-- by the painting coherence HC, and whose composite index paths are
-- identified by the 2-dimensional frame coherence Hpath (isSet in the
-- HSet development).

rew-cohLayer33 :
  {ℓt ℓx ℓp ℓs : Level}
  {T1 : Set ℓt} {T2 T3 : Set ℓs} {X : Set ℓx} {P : X → Set ℓp}
  {S2 : T2 → Set ℓp} {S3 : T3 → Set ℓp}
  {rf0 : T1 → X} {rfF : T2 → X} {rfG : T3 → X}
  {F : (m : T2) → S2 m → P (rfF m)}
  {G : (n : T3) → S3 n → P (rfG n)}
  {d1 d2 : T1} {E1 : d1 ≡ d2}
  {m1 m2 : T2} {C2 : m1 ≡ m2}
  {n1 n2 : T3} {D2 : n1 ≡ n2}
  {C1 : rfF m2 ≡ rf0 d1}
  {D1 : rfG n2 ≡ rf0 d2}
  {K : rfF m1 ≡ rfG n1}
  {aL : S2 m1} {aR : S3 n1}
  → subst P K (F m1 aL) ≡ G n1 aR
  → cong rfF C2 ∙ (C1 ∙ cong rf0 E1) ≡ K ∙ (cong rfG D2 ∙ D1)
  → subst (λ d → P (rf0 d)) E1 (subst P C1 (F m2 (subst S2 C2 aL)))
    ≡ subst P D1 (G n2 (subst S3 D2 aR))
rew-cohLayer33 {P = P} {S2 = S2} {S3 = S3} {rf0 = rf0} {rfF = rfF}
  {rfG = rfG} {F = F} {G = G} {E1 = E1} {m1 = m1} {C2 = C2}
  {n1 = n1} {D2 = D2} {C1 = C1} {D1 = D1} {K = K} {aL = aL} {aR = aR}
  HC Hpath =
  -- fold the left chain into one composite transport of F m1 aL
    cong (λ z → subst (λ d → P (rf0 d)) E1 (subst P C1 z))
         (sym (substCommSlice {S = S2} {P = P} rfF F C2 aL))
  ∙ cong (subst (λ d → P (rf0 d)) E1)
         (sym (substComposite P (cong rfF C2) C1 (F m1 aL)))
  ∙ sym (substComposite P (cong rfF C2 ∙ C1) (cong rf0 E1) (F m1 aL))
  -- reassociate and rewrite the index path with Hpath
  ∙ cong (λ e → subst P e (F m1 aL))
         (∙-assoc (cong rfF C2) C1 (cong rf0 E1) ∙ Hpath)
  -- unfold the right chain
  ∙ substComposite P K (cong rfG D2 ∙ D1) (F m1 aL)
  ∙ cong (subst P (cong rfG D2 ∙ D1)) HC
  ∙ substComposite P (cong rfG D2) D1 (G n1 aR)
  ∙ cong (subst P D1) (substCommSlice {S = S3} {P = P} rfG G D2 aR)

-- The Π-layer bridge (Layer.v's lmap2_rew_eq family, for function
-- layers): a transported layer is determined componentwise.

Π-subst-ext : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
              {d1 d2 : T} (E1 : d1 ≡ d2)
              {f : (ω : A') → B ω d1} {g : (ω : A') → B ω d2}
              → ((ω : A') → subst (B ω) E1 (f ω) ≡ g ω)
              → subst (λ d → (ω : A') → B ω d) E1 f ≡ g
Π-subst-ext {B = B} E1 {f} {g} H =
  J (λ _ E1 → {g : _} → ((ω : _) → subst (B ω) E1 (f ω) ≡ g ω)
              → subst (λ d → (ω : _) → B ω d) E1 f ≡ g)
    (λ {g} H → transportRefl f
               ∙ funExt (λ ω → sym (transportRefl (f ω)) ∙ H ω))
    E1 H
