------------------------------------------------------------------------
-- Bonak.GpdLemmasCoh2 — the two closing lemmas of the νGpd storey:
-- inhabitants of rew-coh2Painting-restr0-Type and rew-coh2Layer-Type
-- (stated at the end of Bonak.GpdLemmas).
--
-- Method: no destruct/J cascade on the statements themselves.  Both
-- goals are of the form
--
--     subst (λ π → subst P π u ≡ w) κ L  ≡  R
--
-- which is (substInPathL, definitionally re-indexed along
-- cong (λ e → subst P e u)) the same as  L ≡ cong (λ e → subst P e u) κ ∙ R.
-- In that form the proof is pure path algebra: every ⊙ unfolds to its
-- algebraic definition (substComposite ∙ cong ∙ q'), every
-- rew-cohLayer33 unfolds to its eight-step chain, and the two sides
-- differ only by
--   * cancellations of the stored data k… against their own inverses,
--   * the naturality of substComposite in its element argument (hnat),
--   * the associativity coherence of substComposite
--     (substComposite-assoc), and
--   * the decomposition sigT-map-eq g q ≡ substCommSlice f g p u ∙ cong (g y) q
--     (sigT-map-eq-decomp).
-- Only those three auxiliary lemmas use J, each with a one-line
-- collapsed point.
--
-- The file also contains permutahedral-paste — the explicit pasting of
-- the seven given hexagons, with EXACTLY the statement of
-- Bonak.GpdLemmas' permutahedral-coherence, meant to replace that
-- definition's Id-kit body (statement unchanged) — and rew-coh2Layer,
-- proven, as rew-coh2Layer-paste.  The pasting calculus it runs on: the
-- flat ⊙-calculus (Sq, ⊙-assoc-Sq, ⊙-whisker-l/r, ⊙-cancel-r), the map
-- lemmas (sigT-map-eq-Sq, scs-comp, sigT-map-eq-⊙), family-Sq, zig3-Sq,
-- twist-Sq, whisker-cancel, and the two edge lemmas map-edge-Sq /
-- k-edge-Sq.  There are no postulates and no holes in this file.
------------------------------------------------------------------------

module Bonak.GpdLemmasCoh2 where

open import Bonak.Prelude
open import Bonak.RewLemmas
open import Bonak.GpdLemmas

private variable
  ℓ ℓ' ℓ'' ℓ''' ℓp ℓq ℓr : Level
  A B : Set ℓ

------------------------------------------------------------------------
-- Small path-algebra kit
------------------------------------------------------------------------

-- Homotopy naturality: a fiberwise family of paths is natural.
hnat : {A : Set ℓ} {B : Set ℓ'} {f g : A → B} (H : (a : A) → f a ≡ g a)
       {a a' : A} (ρ : a ≡ a') → cong f ρ ∙ H a' ≡ H a ∙ cong g ρ
hnat {f = f} {g = g} H {a = a} ρ =
  J (λ a' ρ → cong f ρ ∙ H a' ≡ H a ∙ cong g ρ)
    (sym (lUnit (H a)) ∙ rUnit (H a))
    ρ

-- Right cancellation (mirror of GpdLemmas' ∙-cancel-l).
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
------------------------------------------------------------------------
-- permutahedral-paste — the explicit paste, with EXACTLY the statement
-- of Bonak.GpdLemmas' permutahedral-coherence.
--
-- The six squares that "hold by naturality and don't appear here
-- explicitly" (Rocq's comment) are the six hnat instances below; the
-- seven given hexagons enter as six conjugation squares A1…A6 and the
-- base cell κ.  Writing (in X0)
--
--   α = image of pIs/pV0/gq u0 : rfq (rur zs1) ≡ rf0 (fA u0)
--   β = image of pIr/pV1/gq u1 : rfq (rus zr1) ≡ rf0 (fA u1)
--   γ = image of pIr/pV2/gs u2 : rfs (ruq1 zr1) ≡ rf0 (fB u2)
--   δ = image of pIq/pV3/gs u3 : rfs (rur1 zq1) ≡ rf0 (fB u3)
--   ε = image of pIs/pV4/gr u4 : rfr (ruq1 zs1) ≡ rf0 (fC u4)
--   ζ = image of pIq/pV5/gr u5 : rfr (rus zq1) ≡ rf0 (fC u5)
--
-- HH1/HH3/HH5 (pushed along rfq/rfs/rfr, closed with the naturality of
-- gq/gs/gr) give A1 : α ∙ EA ≡ cong rfq K1 ∙ β, A3, A5; HH2/HH4/HH6
-- (closed with the naturality of KA2/KA4/KA6 in z) give A2, A4, A6.
-- zig3 pastes three such squares into one triangle, cong rf0 κ
-- identifies the two triangles' long sides, and δ cancels on the right.
--
-- Everything from here to permutahedral-paste MOVES WITH the definition
-- into Bonak.GpdLemmas (hnat and ∙-cancel-r, at the top of this file,
-- move too); GpdLemmas already has ∙-assoc, cong-∙ and ∙-cancel-l.
------------------------------------------------------------------------

-- cong of a three-factor composite, distributed.
cong-tri : {A : Set ℓ} {B : Set ℓ'} (f : A → B) {a b c d : A}
           (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
           → cong f (p ∙ (q ∙ r)) ≡ cong f p ∙ (cong f q ∙ cong f r)
cong-tri f p q r = cong-∙ f p (q ∙ r) ∙ cong (cong f p ∙_) (cong-∙ f q r)

-- Right cancellation as an inference rule.
∙-cancel-rᵉ : {x y z : A} {X Y : x ≡ y} (s : y ≡ z) → X ∙ s ≡ Y ∙ s → X ≡ Y
∙-cancel-rᵉ {X = X} {Y = Y} s E =
  sym (∙-cancel-r X s) ∙ cong (_∙ sym s) E ∙ ∙-cancel-r Y s

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


-- The base cell of a K-edge (replaces k-square).
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

-- The base cell of a MAP-edge (replaces map-square).
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

permutahedral-paste :
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
permutahedral-paste
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
-- permutahedral-paste's last step uses ∙-cancel-rʲ so that this round
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
-- permutahedral-paste feeds to zig3) and the fiber square over it.
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

  C : _
  C = cong (λ x → subst (λ dd → S0 (rf0 dd)) E x) kc
      ∙ ( cong (λ x → subst (λ dd → S0 (rf0 dd)) E
                            (subst S0 gu (Fq y1 x))) kb
        ∙ ( rew-cohLayer33 {P = S0} {S2 = S1} {S3 = S1}
              {rf0 = rf0} {rfF = rfq} {rfG = rfs} {F = Fq} {G = Fs}
              {E1 = E} {C2 = pV} {D2 = pV'} {C1 = gu} {D1 = gv}
              {K = KA z2} {aL = Rs z2 c2} {aR = Rq1 z2 c2} (HKA z2 c2) HH
          ∙ ( sym (cong (λ x → subst S0 gv (Fs y2 x)) kb') ∙ sym kc' )))

  restr0Sq : Sq S0 HH (_⊙_ {P = S0} Q₀ (_⊙_ {P = S0} N₀ (refl ∙ C)))
                      (_⊙_ {P = S0} (HKA z2 c2) W)
  restr0Sq = subst→Sq S0 HH
    (rew-coh2Painting-restr0-gen {P = S0} {S2 = S1} {S3 = S1}
       {rq = rfq} {rr = rfs} {r0 = rf0} Fq Fs E pV pV' gu gv (KA z2)
       c2 (Rs z2) (Rq1 z2) (HKA z2 c2) HH b kb b' kb' cc kc cc' kc')

  inner1 : Sq S0 (refl ∙ HH) (_⊙_ {P = S0} Q₀ (_⊙_ {P = S0} N₀ C))
                             (_⊙_ {P = S0} (HKA z2 c2) W)
  inner1 = Sq-∙ S0
    (Sq-of-≡ S0 (cong (λ m → _⊙_ {P = S0} Q₀ (_⊙_ {P = S0} N₀ m)) (lUnit C)))
    restr0Sq

  s1 : _
  s1 = ⊙-assoc-Sq S0 P₀ (_⊙_ {P = S0} Q₀ N₀) C

  s2 : _
  s2 = ⊙-whisker-r S0 P₀ (⊙-assoc-Sq S0 Q₀ N₀ C)

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
-- (v.d) The instantiation.  rew-coh2Layer-Goal is rew-coh2Layer-Type's
-- Set-valued body, verbatim, minus the Hcoh3Frame argument (which the
-- body does not use); post-swap it IS rew-coh2Layer-Type applied.
------------------------------------------------------------------------

rew-coh2Layer-Goal :
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
  → Set ℓp
rew-coh2Layer-Goal
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
  κ HHA Hcoh2Painting =
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
-- rew_coh2Layer, with the Hcoh3Frame premise read against
-- permutahedral-paste (pre-swap spelling).  PROVEN.
------------------------------------------------------------------------

rew-coh2Layer-paste :
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
    HHA ≡ permutahedral-paste {uf0 = uf0} {rf0 = rf0}
            {fA = fA} {fB = fB} {fC = fC}
            {rfq = rfq} {rfs = rfs} {rfr = rfr}
            {gq = gq} {gs = gs} {gr = gr}
            {rur = rur} {rus = rus} {ruq1 = ruq1} {rur1 = rur1}
            {KA2 = KA2} {KA4 = KA4} {KA6 = KA6}
            u0 u1 u2 u3 u4 u5 eU1 eU2 eU3 e2 e4 e6
            zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq
            pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5
            HH1 HH3 HH5 HH2 HH4 HH6 κ)
  → rew-coh2Layer-Goal
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
      κ HHA Hcoh2Painting
rew-coh2Layer-paste
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

  -- base-level copies of permutahedral-paste's internals
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
-- rew_coh2Layer (νGpd/Lemmas.v:253-445) — PROVEN, as
-- rew-coh2Layer-paste above.  No postulates remain in this file.
--
-- Why the statement is spelled with permutahedral-paste rather than
-- through rew-coh2Layer-Type: PRE-SWAP the -Type's Hcoh3Frame premise
-- reads `HHA ≡ permutahedral-coherence …` (the Id-kit body), which is
-- only propositionally equal to `HHA ≡ permutahedral-paste …`, and the
-- -Type cannot be applied without a term of the old premise type.  So
-- the goal is carried by rew-coh2Layer-Goal, which is the -Type's
-- Set-valued body copied verbatim minus the Hcoh3Frame argument (the
-- body does not use it).
--
-- POST-SWAP DERIVATION (one line, after permutahedral-coherence is
-- redefined as permutahedral-paste's body in Bonak.GpdLemmas):
--
--   rew-coh2Layer : <rew-coh2Layer-Type's telescope>
--                 → rew-coh2Layer-Type … κ HHA Hcoh2Painting Hcoh3Frame
--   rew-coh2Layer … κ HHA Hcoh2Painting Hcoh3Frame =
--     rew-coh2Layer-paste … κ HHA Hcoh2Painting Hcoh3Frame
--
-- because (a) rew-coh2Layer-Type's body ignores Hcoh3Frame and is
-- literally rew-coh2Layer-Goal's body, and (b) after the swap
-- `permutahedral-coherence args` and `permutahedral-paste args` unfold
-- to the same term, so the two Hcoh3Frame types are definitionally
-- equal.  Cleanest merge: delete permutahedral-paste from this file at
-- that point and re-point rew-coh2Layer-paste's premise at
-- permutahedral-coherence — then the premise is syntactically the
-- -Type's and the derivation is by η alone.
--
-- Shape of the proof (the (i)-(v) programme, all proven above):
--   Sq→subst turns the goal into a fiber square over κ; ⊙-reindex moves
--   the goal's ⊙'s from S0r/T to S0/X0 (the two re-indexing cells are
--   literally permutahedral-paste's cong-tri factors, so the leftover
--   base equation is pure cancellation); zig3-Sq pastes the six fiber
--   edges into two triangles whose base cells are literally the paste's
--   two zig3's; Hcoh2Painting (via subst→Sq) whiskered by δt joins them;
--   Hcoh3Frame + whisker-cancel identify the resulting base cell with
--   cong (α ∙_) Kap; ⊙-cancel-r drops the reference edge αt.
--   The six edges: map-edge-Sq for C1/C3/C5 (restr0 at level 1, pushed
--   through Fq/Fs/Fr with sigT-map-eq-Sq + sigT-map-eq-⊙, closed with
--   twist-Sq), k-edge-Sq for C2/C4/C6 (restr0 at level 0 + family-Sq for
--   the (z , c)-naturality of HKA2/HKA4/HKA6).  restr0 had to be
--   generalised to three index types (rew-coh2Painting-restr0-gen, from
--   which the GpdLemmas statement is the special case) because the
--   coh2Layer edges have rq, rr, r0 with different domains, exactly as
--   rew-cohLayer33 does.
------------------------------------------------------------------------
