------------------------------------------------------------------------
-- probes.V4-P05-fuel-no-proof — can Bonak.νSet's fuel column drop its
-- EqN proof?
--
-- The proof `.(e : EqN n (p + k))` a νSet member carries is never
-- used computationally: it closes the three impossible-fuel clauses
-- (`layer zero`, `restr-layer zero`, `coh-layer zero`) with an absurd
-- pattern, and it guards `Fil`'s fuel quantifier.  `NoProof` below is
-- the full νSet tower with the proof DELETED: the three absurd
-- clauses become junk clauses (`layer zero … = hunit`, whence the
-- other two are `tt` and `refl` by η-⊤), and `Fil` quantifies over a
-- bare fuel.  `Gate` re-runs the compute gate on it.
--
-- VERDICT: everything typechecks, still with no TERMINATING pragma at
-- --termination-depth=3 (the junk clauses make no calls, so the call
-- graph is νSet's), and `Gate.frame4`'s normal form is byte-identical
-- to the νSet capture.  So the proof column is syntactically
-- dead weight.  It is NOT semantically dead weight, which is why
-- νSet keeps it: without the guard the junk-fuel sector is real
-- structure — `frame m p k D` at a wrong fuel m reduces to an
-- inhabited ⊤-tower (the junk layers are `hunit`), so a filler
-- genuinely carries one HSet-family per wrong fuel, and two ν-sets
-- can differ there.  With the guard those fibers are functions out of
-- an irrelevant ⊥, hence contractible (any two are identified by an
-- absurd irrelevant match under funExt), and the fueled filler type
-- is equivalent to the unfueled one.  This is a mathematical remark
-- about the intended equivalence with the unfueled fillers-only
-- tower, not a mechanized one.
------------------------------------------------------------------------

{-# OPTIONS --rewriting --termination-depth=3 #-}

module probes.V4-P05-fuel-no-proof where

open import Bonak.Prelude
open import Bonak.LeProp
open import Bonak.RewLemmas
open import Bonak.NatRew

module NoProof (arity : Set) where

  record Snoc (A : Set₁) (B : A → Set₁) : Set₁ where
    no-eta-equality; pattern
    constructor _∷_
    field
      pre : A
      fil : B pre
  open Snoc public

  HSet₀ : Set₁
  HSet₀ = HSet lzero

  Pre : ℕ → Set₁
  Fil : (p k : ℕ) (D : Pre (p + k)) → Set₁

  Pre zero    = Unit*
  Pre (suc n) = Snoc (Pre n) (Fil n 0)

  frame : (n p k : ℕ) (D : Pre (p + k)) → HSet₀

  Fil p k D = (m : ℕ) → Dom (frame m p k D) → HSet₀

  layer : (n p k : ℕ) (D : Pre (suc (p + k)))
          (d : Dom (frame n p (suc k) D)) → HSet₀

  painting : (n p k : ℕ) (D : Pre (p + k)) (E : Fil (p + k) 0 D)
             (d : Dom (frame n p k D)) → HSet₀

  restr-frame : (n p k : ℕ) (D : Pre (suc (p + k)))
                (q : ℕ) .(Hq : q ≤ k) (ε : arity)
                (d : Dom (frame (suc n) p (suc k) D))
                → Dom (frame n p k (pre D))

  restr-layer : (n p k : ℕ) (D : Pre (suc (suc (p + k))))
                (q : ℕ) .(Hq : q ≤ k) (ε : arity)
                (d : Dom (frame (suc n) p (suc (suc k)) D))
                (l : Dom (layer (suc n) p (suc k) D d))
                → Dom (layer n p k (pre D)
                         (restr-frame n p (suc k) D (suc q) Hq ε d))

  restr-painting : (n p k : ℕ)
                   (D : Pre (suc (p + k))) (E : Fil (suc (p + k)) 0 D)
                   (q : ℕ) .(Hq : q ≤ k) (ε : arity)
                   (d : Dom (frame (suc n) p (suc k) D))
                   (c : Dom (painting (suc n) p (suc k) D E d))
                   → Dom (painting n p k (pre D) (fil D)
                            (restr-frame n p k D q Hq ε d))

  coh-frame : (n p k : ℕ) (D : Pre (suc (suc (p + k))))
              (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
              (d : Dom (frame (suc (suc n)) p (suc (suc k)) D))
              → restr-frame n p k (pre D) q Hq ε
                  (restr-frame (suc n) p (suc k) D r
                     (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
                ≡ restr-frame n p k (pre D) r (le-trans r q k Hr Hq) ω
                    (restr-frame (suc n) p (suc k) D (suc q) Hq ε d)

  coh-layer : (n p k : ℕ) (D : Pre (suc (suc (suc (p + k)))))
              (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
              (d : Dom (frame (suc (suc n)) p (suc (suc (suc k))) D))
              (l : Dom (layer (suc (suc n)) p (suc (suc k)) D d))
              → subst (λ x → Dom (layer n p k (pre (pre D)) x))
                  (coh-frame n p (suc k) D (suc q) Hq (suc r) Hr ε ω d)
                  (restr-layer n p k (pre D) q Hq ε
                     (restr-frame (suc n) p (suc (suc k)) D (suc r)
                        (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
                     (restr-layer (suc n) p (suc k) D r
                        (le-trans r q (suc k) Hr (le-up q k Hq)) ω d l))
                ≡ restr-layer n p k (pre D) r (le-trans r q k Hr Hq) ω
                    (restr-frame (suc n) p (suc (suc k)) D (suc (suc q))
                       Hq ε d)
                    (restr-layer (suc n) p (suc k) D (suc q) Hq ε d l)

  coh-painting : (n p k : ℕ) (D : Pre (suc (suc (p + k))))
                 (E : Fil (suc (suc (p + k))) 0 D)
                 (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
                 (d : Dom (frame (suc (suc n)) p (suc (suc k)) D))
                 (c : Dom (painting (suc (suc n)) p (suc (suc k)) D E d))
                 → subst (λ x → Dom (painting n p k (pre (pre D))
                                       (fil (pre D)) x))
                     (coh-frame n p k D q Hq r Hr ε ω d)
                     (restr-painting n p k (pre D) (fil D) q Hq ε
                        (restr-frame (suc n) p (suc k) D r
                           (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
                        (restr-painting (suc n) p (suc k) D E r
                           (le-trans r q (suc k) Hr (le-up q k Hq)) ω d c))
                   ≡ restr-painting n p k (pre D) (fil D) r
                       (le-trans r q k Hr Hq) ω
                       (restr-frame (suc n) p (suc k) D (suc q) Hq ε d)
                       (restr-painting (suc n) p (suc k) D E (suc q)
                          Hq ε d c)

  frame n zero    k D = hunit
  frame n (suc p) k D =
    hΣ (frame n p (suc k) D) (λ d → layer n p k D d)

  -- The junk clause: at an exhausted fuel the layer is trivial.
  layer zero    p k D d = hunit
  layer (suc n) p k (D ∷ E) d =
    hΠ arity (λ ε → painting n p k D E
                      (restr-frame n p k (D ∷ E) 0 tt ε d))

  painting n p zero    D E d = E n d
  painting n p (suc k) D E d =
    hΣ (layer n p k D d) (λ l → painting n (suc p) k D E (d , l))

  restr-frame n zero    k D q Hq ε d       = tt
  restr-frame n (suc p) k D q Hq ε (d , l) =
    restr-frame n p (suc k) D (suc q) Hq ε d ,
    restr-layer n p k D q Hq ε d l

  restr-layer zero    p k D q Hq ε d l = tt
  restr-layer (suc n) p k ((D ∷ E₁) ∷ E₂) q Hq ε d l ω =
    subst (λ x → Dom (painting n p k D E₁ x))
      (coh-frame n p k ((D ∷ E₁) ∷ E₂) q Hq 0 tt ε ω d)
      (restr-painting n p k (D ∷ E₁) E₂ q Hq ε
        (restr-frame (suc n) p (suc k) ((D ∷ E₁) ∷ E₂) 0 tt ω d) (l ω))

  restr-painting n p k       (D ∷ E₁) E zero    Hq ε d (l , c) = l ε
  restr-painting n p zero    D        E (suc q) ()
  restr-painting n p (suc k) (D ∷ E₁) E (suc q) Hq ε d (l , c) =
    restr-layer n p k (D ∷ E₁) q Hq ε d l ,
    restr-painting n (suc p) k (D ∷ E₁) E q Hq ε (d , l) c

  coh-frame n zero    k D q Hq r Hr ε ω d       = refl
  coh-frame n (suc p) k D q Hq r Hr ε ω (d , l) =
    Σ≡ (coh-frame n p (suc k) D (suc q) Hq (suc r) Hr ε ω d)
       (coh-layer n p k D q Hq r Hr ε ω d l)

  coh-layer zero    p k D q Hq r Hr ε ω d l = refl
  coh-layer (suc n) p k (((D ∷ E₁) ∷ E₂) ∷ E₃) q Hq r Hr ε ω d l =
    Π-subst-ext
      {B = λ θ x → Dom (painting n p k D E₁
                          (restr-frame n p k P₁ 0 tt θ x))}
      (coh-frame (suc n) p (suc k) P₃ (suc q) Hq (suc r) Hr ε ω d)
      (λ θ → rew-cohLayer33
        {P = λ x → Dom (painting n p k D E₁ x)}
        {S2 = λ m → Dom (painting (suc n) p (suc k) P₁ E₂ m)}
        {S3 = λ m → Dom (painting (suc n) p (suc k) P₁ E₂ m)}
        {rf0 = λ x → restr-frame n p k P₁ 0 tt θ x}
        {rfF = λ m → restr-frame n p k P₁ q Hq ε m}
        {rfG = λ m → restr-frame n p k P₁ r H₂ ω m}
        {F = λ m c → restr-painting n p k P₁ E₂ q Hq ε m c}
        {G = λ m c → restr-painting n p k P₁ E₂ r H₂ ω m c}
        {E1 = coh-frame (suc n) p (suc k) P₃ (suc q) Hq (suc r) Hr ε ω d}
        {m1 = restr-frame (suc n) p (suc k) P₂ r H₁ ω (b θ)}
        {m2 = restr-frame (suc n) p (suc k) P₂ 0 tt θ dR}
        {C2 = coh-frame (suc n) p (suc k) P₃ r H₁ 0 tt ω θ d}
        {n1 = restr-frame (suc n) p (suc k) P₂ (suc q) Hq ε (b θ)}
        {n2 = restr-frame (suc n) p (suc k) P₂ 0 tt θ dE}
        {D2 = coh-frame (suc n) p (suc k) P₃ (suc q) Hq 0 tt ε θ d}
        {C1 = coh-frame n p k P₂ q Hq 0 tt ε θ dR}
        {D1 = coh-frame n p k P₂ r H₂ 0 tt ω θ dE}
        {K = coh-frame n p k P₂ q Hq r Hr ε ω (b θ)}
        {aL = restr-painting (suc n) p (suc k) P₂ E₃ r H₁ ω (b θ) (l θ)}
        {aR = restr-painting (suc n) p (suc k) P₂ E₃ (suc q) Hq ε
                (b θ) (l θ)}
        (coh-painting n p k P₂ E₃ q Hq r Hr ε ω (b θ) (l θ))
        (isSetDom (frame n p k D) _ _ _ _))
    where
    P₁ = (D ∷ E₁)
    P₂ = ((D ∷ E₁) ∷ E₂)
    P₃ = (((D ∷ E₁) ∷ E₂) ∷ E₃)
    H₁ = le-trans r q (suc k) Hr (le-up q k Hq)
    H₂ = le-trans r q k Hr Hq
    dR = restr-frame (suc (suc n)) p (suc (suc k)) P₃ (suc r) H₁ ω d
    dE = restr-frame (suc (suc n)) p (suc (suc k)) P₃ (suc (suc q)) Hq ε d
    b : (θ : arity) → Dom (frame (suc (suc n)) p (suc (suc k)) P₂)
    b θ = restr-frame (suc (suc n)) p (suc (suc k)) P₃ 0 tt θ d

  coh-painting n p k ((D ∷ E₁) ∷ E₂) E q Hq zero Hr ε ω d (l , c) = refl
  coh-painting n p k       D          E zero    Hq (suc r) ()
  coh-painting n p zero    D          E (suc q) ()
  coh-painting n p (suc k) ((D ∷ E₁) ∷ E₂) E (suc q) Hq (suc r) Hr ε ω
               d (l , c) =
    Σ≡dep {P = λ x → Dom (layer n p k D x)}
          {Q = λ z → Dom (painting n (suc p) k D E₁ z)}
      (coh-frame n p (suc k) ((D ∷ E₁) ∷ E₂) (suc q) Hq (suc r) Hr ε ω d)
      (coh-layer n p k ((D ∷ E₁) ∷ E₂) q Hq r Hr ε ω d l)
      (coh-painting n (suc p) k ((D ∷ E₁) ∷ E₂) E q Hq r Hr ε ω (d , l) c)

------------------------------------------------------------------------
-- The gate.
------------------------------------------------------------------------

module Gate = NoProof ⊤

pt4 : Gate.Pre 4
pt4 = ((((tt* Gate.∷ (λ m d → hunit)) Gate.∷ (λ m d → hunit))
        Gate.∷ (λ m d → hunit)) Gate.∷ (λ m d → hunit))

frame4 : Set
frame4 = Dom (Gate.frame 4 4 0 pt4)
