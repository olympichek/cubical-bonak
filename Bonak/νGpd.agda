------------------------------------------------------------------------
-- Bonak.νGpd — the groupoid storey of the tower, with fillers-only
-- storage, relative (p , k) indices, a checked dimension column, and
-- PathP-shaped coherences.
--
-- What changes at the groupoid level:
--
-- * Frames, layers and paintings are HGpds (gunit / gΣ / gΠ).
-- * The layer coherence can no longer close by square filling in an
--   HSet of frames: the square it needs — the three-face hexagon in
--   Square form — becomes the stored-by-computation 2-coherence
--   `coh2-frame`, and the mutual block grows one more storey:
--   coh2-frame / coh2-layer / coh2-painting, shaped exactly like
--   coh-frame / coh-layer / coh-painting one level up, with squares
--   for paths and dependent squares for dependent paths.
-- * The s = 0 painting 2-coherence is the filler of the layer
--   coherence's square composition (Bonak.GpdLemmas' cohLayer-fillP),
--   exactly as the r = 0 painting coherence is subst-filler of
--   restr-layer's transport one storey down.
-- * The only truncation site is isGroupoid→Cube inside coh2-layer: the
--   four-face permutahedron cube in the HGpd of frames.
-- * Termination stays checked, no pragma: the coh2 statements write
--   occurrences up to suc⁴ of the member's dimension (coh2-layer's
--   premise pack lives four storeys up), so the call matrices carry
--   +4 increases and the checker needs --termination-depth=4, exactly
--   as Bonak.νSet's +3 statements need depth 3; depth 3 rejects the
--   restr-frame..coh2-layer-suc group.
------------------------------------------------------------------------

{-# OPTIONS --rewriting --termination-depth=4 #-}

module Bonak.νGpd (arity : Set) where

open import Bonak.Prelude
open import Bonak.LeProp
open import Bonak.RewLemmas
open import Bonak.GpdLemmas
open import Bonak.NatRew

HGpd₀ : Set₁
HGpd₀ = HGpd lzero

-- The no-eta cons cell prevents fieldwise eta-expansion when prefixes are
-- compared.
record Snoc (A : Set₁) (B : A → Set₁) : Set₁ where
  no-eta-equality; pattern
  constructor _∷_
  field
    pre : A
    fil : B pre
open Snoc public

------------------------------------------------------------------------
-- The block: signatures
------------------------------------------------------------------------

-- The prefix of fillers, and the filler over one.
Pre : ℕ → Set₁
Fil : (p k : ℕ) (D : Pre (p + k)) → Set₁

Pre zero    = Unit*
Pre (n +1) = Snoc (Pre n) (Fil n 0)

-- frame(p) at dimension p + k, carried as the argument n ~ p + k.
frame : (n p k : ℕ) .(e : EqN n (p + k)) (D : Pre (p + k)) → HGpd₀

-- A filler eats a point of the full frame at any dimension.
Fil p k D = (m : ℕ) .(f : EqN m (p + k)) → GDom (frame m p k f D) → HGpd₀

-- layer(p) at dimension p + k + 1; its dimension argument is its point's.
layer : (n p k : ℕ) .(e : EqN n (p + k +1)) (D : Pre (p + k +1))
        (d : GDom (frame n p (k +1) e D)) → HGpd₀

-- painting(p) at dimension p + k, over the filler E.
painting : (n p k : ℕ) .(e : EqN n (p + k)) (D : Pre (p + k))
           (E : Fil (p + k) 0 D)
           (d : GDom (frame n p k e D)) → HGpd₀

-- The three restrictions: dimension p + k + 1 ↦ dimension p + k along
-- the q-th face (q ≤ k); the dimension argument is the output's,
-- the input's is suc of it.
restr-frame : (n p k : ℕ) .(e : EqN n (p + k))
              (D : Pre (p + k +1))
              (q : ℕ) .(Hq : q ≤ k) (ε : arity)
              (d : GDom (frame (n +1) p (k +1) e D))
              → GDom (frame n p k e (pre D))

restr-layer : (n p k : ℕ) .(e : EqN n (p + k +1))
              (D : Pre (p + k +2))
              (q : ℕ) .(Hq : q ≤ k) (ε : arity)
              (d : GDom (frame (n +1) p (k +2) e D))
              (l : GDom (layer (n +1) p (k +1) e D d))
              → GDom (layer n p k e (pre D)
                        (restr-frame n p (k +1) e D (q +1) Hq ε d))

restr-painting : (n p k : ℕ) .(e : EqN n (p + k))
                 (D : Pre (p + k +1)) (E : Fil (p + k +1) 0 D)
                 (q : ℕ) .(Hq : q ≤ k) (ε : arity)
                 (d : GDom (frame (n +1) p (k +1) e D))
                 (c : GDom (painting (n +1) p (k +1) e D E d))
                 → GDom (painting n p k e (pre D) (fil D)
                           (restr-frame n p k e D q Hq ε d))

-- The three coherences: the faces q and r commute (r ≤ q ≤ k); the
-- dimension argument is the final output's, two below the point's.
coh-frame : (n p k : ℕ) .(e : EqN n (p + k))
            (D : Pre (p + k +2))
            (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
            (d : GDom (frame (n +2) p (k +2) e D))
            → restr-frame n p k e (pre D) q Hq ε
                (restr-frame (n +1) p (k +1) e D r
                   (le-trans r q (k +1) Hr (le-up q k Hq)) ω d)
              ≡ restr-frame n p k e (pre D) r (le-trans r q k Hr Hq) ω
                  (restr-frame (n +1) p (k +1) e D (q +1) Hq ε d)

coh-layer : (n p k : ℕ) .(e : EqN n (p + k +1))
            (D : Pre (p + k +3))
            (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
            (d : GDom (frame (n +2) p (k +3) e D))
            (l : GDom (layer (n +2) p (k +2) e D d))
            → PathP (λ i → GDom (layer n p k e (pre (pre D))
                       (coh-frame n p (k +1) e D (q +1) Hq (r +1) Hr ε ω d i)))
                (restr-layer n p k e (pre D) q Hq ε
                   (restr-frame (n +1) p (k +2) e D (r +1)
                      (le-trans r q (k +1) Hr (le-up q k Hq)) ω d)
                   (restr-layer (n +1) p (k +1) e D r
                      (le-trans r q (k +1) Hr (le-up q k Hq)) ω d l))
                (restr-layer n p k e (pre D) r (le-trans r q k Hr Hq) ω
                   (restr-frame (n +1) p (k +2) e D (q +2) Hq ε d)
                   (restr-layer (n +1) p (k +1) e D (q +1) Hq ε d l))

coh-painting : (n p k : ℕ) .(e : EqN n (p + k))
               (D : Pre (p + k +2))
               (E : Fil (p + k +2) 0 D)
               (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
               (d : GDom (frame (n +2) p (k +2) e D))
               (c : GDom (painting (n +2) p (k +2) e D E d))
               → PathP (λ i → GDom (painting n p k e (pre (pre D)) (fil (pre D))
                          (coh-frame n p k e D q Hq r Hr ε ω d i)))
                   (restr-painting n p k e (pre D) (fil D) q Hq ε
                      (restr-frame (n +1) p (k +1) e D r
                         (le-trans r q (k +1) Hr (le-up q k Hq)) ω d)
                      (restr-painting (n +1) p (k +1) e D E r
                         (le-trans r q (k +1) Hr (le-up q k Hq)) ω d c))
                   (restr-painting n p k e (pre D) (fil D) r
                      (le-trans r q k Hr Hq) ω
                      (restr-frame (n +1) p (k +1) e D (q +1) Hq ε d)
                      (restr-painting (n +1) p (k +1) e D E (q +1) Hq ε d c))

-- The three 2-coherences: the faces q, r and s commute (s ≤ r ≤ q ≤ k);
-- the dimension argument is the final output's, three below the point's. The
-- 2-dimensional frame coherence is the three-face hexagon in Square
-- form — the square coh-layer's proof consumes, with the s-th face
-- generalized from the layer direction (s = 0) to any s ≤ r: the
-- coherence at the s-restricted point connects, along the s-restriction
-- of the one-level-up coherence, the two conjugation composites.
coh2-frame : (n p k : ℕ) .(e : EqN n (p + k))
             (D : Pre (p + k +3))
             (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q)
             (s : ℕ) .(Hs : s ≤ r) (ε ω θ : arity)
             (d : GDom (frame (n +3) p (k +3) e D))
             → Square
                 (coh-frame n p k e (pre D) q Hq r Hr ε ω
                    (restr-frame (n +2) p (k +2) e D s
                       (le-up s (k +1) (le-up s k
                          (le-trans s r k Hs (le-trans r q k Hr Hq)))) θ d))
                 (cong (restr-frame n p k e (pre (pre D)) s
                          (le-trans s r k Hs (le-trans r q k Hr Hq)) θ)
                    (coh-frame (n +1) p (k +1) e D
                       (q +1) Hq (r +1) Hr ε ω d))
                 (cong (restr-frame n p k e (pre (pre D)) q Hq ε)
                    (coh-frame (n +1) p (k +1) e D r
                       (le-trans r q (k +1) Hr (le-up q k Hq)) s Hs ω θ d)
                  ∙ coh-frame n p k e (pre D) q Hq s
                      (le-trans s r q Hs Hr) ε θ
                      (restr-frame (n +2) p (k +2) e D
                         (r +1) (le-trans r q (k +1) Hr (le-up q k Hq)) ω d))
                 (cong (restr-frame n p k e (pre (pre D)) r
                          (le-trans r q k Hr Hq) ω)
                    (coh-frame (n +1) p (k +1) e D (q +1) Hq s
                       (le-up s q (le-trans s r q Hs Hr)) ε θ d)
                  ∙ coh-frame n p k e (pre D) r (le-trans r q k Hr Hq) s Hs ω θ
                      (restr-frame (n +2) p (k +2) e D (q +2) Hq ε d))

coh2-layer : (n p k : ℕ) .(e : EqN n (p + k +1))
             (D : Pre (p + k +4))
             (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q)
             (s : ℕ) .(Hs : s ≤ r) (ε ω θ : arity)
             (d : GDom (frame (n +3) p (k +4) e D))
             (l : GDom (layer (n +3) p (k +3) e D d))
             → SquareP
                 (λ i j → GDom (layer n p k e (pre (pre (pre D)))
                    (coh2-frame n p (k +1) e D (q +1) Hq (r +1) Hr
                       (s +1) Hs ε ω θ d i j)))
                 (coh-layer n p k e (pre D) q Hq r Hr ε ω
                    (restr-frame (n +2) p (k +3) e D (s +1)
                       (le-up s (k +1) (le-up s k
                          (le-trans s r k Hs (le-trans r q k Hr Hq)))) θ d)
                    (restr-layer (n +2) p (k +2) e D s
                       (le-up s (k +1) (le-up s k
                          (le-trans s r k Hs (le-trans r q k Hr Hq)))) θ d l))
                 (λ i → restr-layer n p k e (pre (pre D)) s
                          (le-trans s r k Hs (le-trans r q k Hr Hq)) θ
                          (coh-frame (n +1) p (k +2) e D
                             (q +2) Hq (r +2) Hr ε ω d i)
                          (coh-layer (n +1) p (k +1) e D
                             (q +1) Hq (r +1) Hr ε ω d l i))
                 (compPathP
                    {P = λ x → GDom (layer n p k e (pre (pre (pre D)))
                                       x)}
                    (λ i → restr-layer n p k e (pre (pre D)) q Hq ε
                             (coh-frame (n +1) p (k +2) e D (r +1)
                                (le-trans r q (k +1) Hr (le-up q k Hq)) (s +1) Hs ω θ d i)
                             (coh-layer (n +1) p (k +1) e D r
                                (le-trans r q (k +1) Hr (le-up q k Hq)) s Hs ω θ d l i))
                    (coh-layer n p k e (pre D) q Hq s
                       (le-trans s r q Hs Hr) ε θ
                       (restr-frame (n +2) p (k +3) e D (r +2)
                          (le-trans r q (k +1) Hr (le-up q k Hq)) ω d)
                       (restr-layer (n +2) p (k +2) e D (r +1)
                          (le-trans r q (k +1) Hr (le-up q k Hq)) ω d l)))
                 (compPathP
                    {P = λ x → GDom (layer n p k e (pre (pre (pre D))) x)}
                    (λ i → restr-layer n p k e (pre (pre D)) r
                             (le-trans r q k Hr Hq) ω
                             (coh-frame (n +1) p (k +2) e D (q +2) Hq (s +1)
                                (le-up s q (le-trans s r q Hs Hr)) ε θ d i)
                             (coh-layer (n +1) p (k +1) e D (q +1) Hq s
                                (le-up s q (le-trans s r q Hs Hr)) ε θ d l i))
                    (coh-layer n p k e (pre D) r (le-trans r q k Hr Hq) s Hs ω θ
                       (restr-frame (n +2) p (k +3) e D (q +3) Hq ε d)
                       (restr-layer (n +2) p (k +2) e D (q +2) Hq ε d l)))

-- The recursive layer 2-coherence at a fixed point of the arity: the
-- (i , j)-square of the goal's θ'-applied faces. A separate member so
-- that the interval directions are λ-bound rather than clause
-- patterns: the giant body is then checked against its boundary once,
-- by the path-abstraction rule, and coh2-layer's own clause is a
-- one-application body whose boundary matches syntactically (interval
-- clause patterns additionally trigger the checker's boundary-
-- confluence pass, which normalizes and reifies the clause body per
-- face — prohibitive at this term size).
Coh2LayerSucT : (n p k : ℕ) .(e : EqN (n +1) (p + k +1))
                 (D : Pre (p + k)) (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (p + k +1) 0 (D ∷ E₁))
                 (E₃ : Fil (p + k +2) 0 ((D ∷ E₁) ∷ E₂))
                 (E₄ : Fil (p + k +3) 0 (((D ∷ E₁) ∷ E₂) ∷ E₃))
                 (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q)
                 (s : ℕ) .(Hs : s ≤ r) (ε ω θ : arity)
                 (d : GDom (frame (n +4) p (k +4) e ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)))
                 (l : GDom (layer (n +4) p (k +3) e ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) d))
                 (θ' : arity)
                 → Set
coh2-layer-suc : (n p k : ℕ) .(e : EqN (n +1) (p + k +1))
                 (D : Pre (p + k)) (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (p + k +1) 0 (D ∷ E₁))
                 (E₃ : Fil (p + k +2) 0 ((D ∷ E₁) ∷ E₂))
                 (E₄ : Fil (p + k +3) 0 (((D ∷ E₁) ∷ E₂) ∷ E₃))
                 (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q)
                 (s : ℕ) .(Hs : s ≤ r) (ε ω θ : arity)
                 (d : GDom (frame (n +4) p (k +4) e ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)))
                 (l : GDom (layer (n +4) p (k +3) e ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) d))
                 (θ' : arity)
                 → Coh2LayerSucT n p k e D E₁ E₂ E₃ E₄ q Hq r Hr s Hs ε ω θ d l θ'

coh2-painting : (n p k : ℕ) .(e : EqN n (p + k))
                (D : Pre (p + k +3))
                (E : Fil (p + k +3) 0 D)
                (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q)
                (s : ℕ) .(Hs : s ≤ r) (ε ω θ : arity)
                (d : GDom (frame (n +3) p (k +3) e D))
                (c : GDom (painting (n +3) p (k +3) e D E d))
                → SquareP
                    (λ i j → GDom (painting n p k e (pre (pre (pre D)))
                       (fil (pre (pre D)))
                       (coh2-frame n p k e D q Hq r Hr s Hs ε ω θ d i j)))
                    (coh-painting n p k e (pre D) (fil D) q Hq r Hr ε ω
                       (restr-frame (n +2) p (k +2) e D s
                          (le-up s (k +1) (le-up s k
                             (le-trans s r k Hs (le-trans r q k Hr Hq)))) θ d)
                       (restr-painting (n +2) p (k +2) e D E s
                          (le-up s (k +1) (le-up s k
                             (le-trans s r k Hs (le-trans r q k Hr Hq)))) θ d c))
                    (λ i → restr-painting n p k e (pre (pre D)) (fil (pre D)) s
                             (le-trans s r k Hs (le-trans r q k Hr Hq)) θ
                             (coh-frame (n +1) p (k +1) e D (q +1) Hq (r +1) Hr ε ω d i)
                             (coh-painting (n +1) p (k +1) e D E (q +1) Hq (r +1) Hr ε ω d c i))
                 (compPathP
                       {P = λ x → GDom (painting n p k e (pre (pre (pre D))) (fil (pre (pre D))) x)}
                       (λ i → restr-painting n p k e (pre (pre D)) (fil (pre D)) q Hq ε
                                (coh-frame (n +1) p (k +1) e D r
                                   (le-trans r q (k +1) Hr (le-up q k Hq)) s Hs ω θ d i)
                                (coh-painting (n +1) p (k +1) e D E r
                                   (le-trans r q (k +1) Hr (le-up q k Hq)) s Hs ω θ d c i))
                       (coh-painting n p k e (pre D) (fil D) q Hq s
                          (le-trans s r q Hs Hr) ε θ
                          (restr-frame (n +2) p (k +2) e D (r +1)
                             (le-trans r q (k +1) Hr (le-up q k Hq)) ω d)
                          (restr-painting (n +2) p (k +2) e D E (r +1)
                             (le-trans r q (k +1) Hr (le-up q k Hq)) ω d c)))
                 (compPathP
                       {P = λ x → GDom (painting n p k e (pre (pre (pre D))) (fil (pre (pre D))) x)}
                       (λ i → restr-painting n p k e (pre (pre D))
                                (fil (pre D)) r (le-trans r q k Hr Hq) ω
                                (coh-frame (n +1) p (k +1) e D (q +1) Hq s
                                   (le-up s q (le-trans s r q Hs Hr)) ε θ d i)
                                (coh-painting (n +1) p (k +1) e D E (q +1) Hq s
                                   (le-up s q (le-trans s r q Hs Hr)) ε θ d c i))
                       (coh-painting n p k e (pre D) (fil D) r
                          (le-trans r q k Hr Hq) s Hs ω θ
                          (restr-frame (n +2) p (k +2) e D (q +2) Hq ε d)
                          (restr-painting (n +2) p (k +2) e D E (q +2) Hq ε d c)))

------------------------------------------------------------------------
-- The block: definitions
------------------------------------------------------------------------

frame n zero    k e D = gunit
frame n (p +1) k e D =
  gΣ (frame n p (k +1) e D) (λ d → layer n p k e D d)

layer zero    p k ()
layer (n +1) p k e (D ∷ E) d =
  gΠ arity (λ ε → painting n p k e D E
                    (restr-frame n p k e (D ∷ E) 0 tt ε d))

painting n p zero    e D E d = E n e d
painting n p (k +1) e D E d =
  gΣ (layer n p k e D d) (λ l → painting n (p +1) k e D E (d , l))

restr-frame n zero    k e D q Hq ε d       = tt
restr-frame n (p +1) k e D q Hq ε (d , l) =
  restr-frame n p (k +1) e D (q +1) Hq ε d ,
  restr-layer n p k e D q Hq ε d l

restr-layer zero    p k ()
restr-layer (n +1) p k e ((D ∷ E₁) ∷ E₂) q Hq ε d l ω =
  subst (λ x → GDom (painting n p k e D E₁ x))
    (coh-frame n p k e ((D ∷ E₁) ∷ E₂) q Hq 0 tt ε ω d)
    (restr-painting n p k e (D ∷ E₁) E₂ q Hq ε
      (restr-frame (n +1) p (k +1) e ((D ∷ E₁) ∷ E₂) 0 tt ω d) (l ω))

restr-painting n p k       e (D ∷ E₁) E zero    Hq ε d (l , c) = l ε
restr-painting n p zero    e D        E (q +1) ()
restr-painting n p (k +1) e (D ∷ E₁) E (q +1) Hq ε d (l , c) =
  restr-layer n p k e (D ∷ E₁) q Hq ε d l ,
  restr-painting n (p +1) k e (D ∷ E₁) E q Hq ε (d , l) c

coh-frame n zero    k e D q Hq r Hr ε ω d         = refl
coh-frame n (p +1) k e D q Hq r Hr ε ω (d , l) i =
  coh-frame n p (k +1) e D (q +1) Hq (r +1) Hr ε ω d i ,
  coh-layer n p k e D q Hq r Hr ε ω d l i

-- The layer coherence closes with the s = 0 instance of the
-- 2-dimensional frame coherence because frames are groupoids rather than
-- sets.
coh-layer zero    p k ()
coh-layer (n +1) p k e (((D ∷ E₁) ∷ E₂) ∷ E₃) q Hq r Hr ε ω d l i θ =
  cohLayer-squareP
    {P = λ x → GDom (painting n p k e D E₁ x)}
    {S2 = λ m → GDom (painting (n +1) p (k +1) e P₁ E₂ m)}
    {S3 = λ m → GDom (painting (n +1) p (k +1) e P₁ E₂ m)}
    {rf0 = λ x → restr-frame n p k e P₁ 0 tt θ x}
    {rfF = λ m → restr-frame n p k e P₁ q Hq ε m}
    {rfG = λ m → restr-frame n p k e P₁ r H₂ ω m}
    {F = λ m c → restr-painting n p k e P₁ E₂ q Hq ε m c}
    {G = λ m c → restr-painting n p k e P₁ E₂ r H₂ ω m c}
    {E1 = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq (r +1) Hr ε ω d}
    {m1 = restr-frame (n +1) p (k +1) e P₂ r H₁ ω (b θ)}
    {m2 = restr-frame (n +1) p (k +1) e P₂ 0 tt θ dR}
    {C2 = coh-frame (n +1) p (k +1) e P₃ r H₁ 0 tt ω θ d}
    {n1 = restr-frame (n +1) p (k +1) e P₂ (q +1) Hq ε (b θ)}
    {n2 = restr-frame (n +1) p (k +1) e P₂ 0 tt θ dE}
    {D2 = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq 0 tt ε θ d}
    {C1 = coh-frame n p k e P₂ q Hq 0 tt ε θ dR}
    {D1 = coh-frame n p k e P₂ r H₂ 0 tt ω θ dE}
    {K = coh-frame n p k e P₂ q Hq r Hr ε ω (b θ)}
    {aL = restr-painting (n +1) p (k +1) e P₂ E₃ r H₁ ω (b θ) (l θ)}
    {aR = restr-painting (n +1) p (k +1) e P₂ E₃ (q +1) Hq ε (b θ) (l θ)}
    (coh-painting n p k e P₂ E₃ q Hq r Hr ε ω (b θ) (l θ))
    (coh2-frame n p k e P₃ q Hq r Hr 0 tt ε ω θ d) i where
  P₁ = (D ∷ E₁)
  P₂ = ((D ∷ E₁) ∷ E₂)
  P₃ = (((D ∷ E₁) ∷ E₂) ∷ E₃)
  H₁ = le-trans r q (k +1) Hr (le-up q k Hq)
  H₂ = le-trans r q k Hr Hq
  -- the ω-restriction of d used by the outer restr-layer on each side,
  dR = restr-frame (n +2) p (k +2) e P₃ (r +1) H₁ ω d
  dE = restr-frame (n +2) p (k +2) e P₃ (q +2) Hq ε d
  -- and its θ-restriction, where the painting coherence applies.
  b : (θ : arity) → GDom (frame (n +2) p (k +2) e P₂)
  b θ = restr-frame (n +2) p (k +2) e P₃ 0 tt θ d

-- The painting coherence. With Π-layers the r = 0 case is the filler
-- of restr-layer's transport (both endpoints reduce to the same
-- restr-painting composite, one transported); the r , q ≥ 1 case pairs
-- the layer coherence with the recursive painting coherence — the pair
-- path is the clause coh-frame unfolds to, so the alignment holds by
-- clause unfolding rather than by a stored-term discipline.
-- Without eta on the prefix the r = 0 reduction (`restr-painting … 0`
-- ↦ `l ω`) fires only when the prefix is a constructor, so this
-- clause has to match it even though the proof does not use it.
coh-painting n p k e ((D ∷ E₁) ∷ E₂) E q Hq zero Hr ε ω d (l , c) =
  subst-filler (λ x → GDom (painting n p k e D E₁ x))
    (coh-frame n p k e ((D ∷ E₁) ∷ E₂) q Hq 0 tt ε ω d)
    (restr-painting n p k e (D ∷ E₁) E₂ q Hq ε
      (restr-frame (n +1) p (k +1) e ((D ∷ E₁) ∷ E₂) 0 tt ω d) (l ω))
coh-painting n p k e       D          E zero    Hq (r +1) ()
coh-painting n p zero    e D        E (q +1) ()
coh-painting n p (k +1) e ((D ∷ E₁) ∷ E₂) E (q +1) Hq (r +1) Hr ε ω d (l , c) i =
  coh-layer n p k e ((D ∷ E₁) ∷ E₂) q Hq r Hr ε ω d l i ,
  coh-painting n (p +1) k e ((D ∷ E₁) ∷ E₂) E q Hq r Hr ε ω (d , l) c i

-- The frame 2-coherence pairs the recursive frame square with the
-- layer square; its composite boundaries compute componentwise.
coh2-frame n zero    k e D q Hq r Hr s Hs ε ω θ d = λ _ _ → tt
coh2-frame n (p +1) k e D q Hq r Hr s Hs ε ω θ (d , l) i j =
  coh2-frame n p (k +1) e D (q +1) Hq (r +1) Hr (s +1) Hs ε ω θ d i j ,
  coh2-layer n p k e D q Hq r Hr s Hs ε ω θ d l i j

-- The layer 2-coherence: the four-face permutahedron. Pointwise in
-- θ', the goal square is the coh2-painting premise at the
-- θ'-restricted point, transported over the isGroupoid→Cube interior
-- (the storey's one truncation site) along four lateral squares:
-- each is the vertical composite of a conjugation square — the
-- premise's face carried along the r = 0 frame coherence κ by
-- application — with the canonical filler of the corresponding goal
-- face (cohLayer-fillP for the coherence faces, subst-filler for the
-- transport face), the composite faces joined pointwise by ∙sliceP
-- and their junction edges aligned by cong²Funct + assocP cells.
-- The goal's composite faces are Π-valued composites applied at θ',
-- and comp in a Π-type evaluates through the function direction, so
-- the cube is built with the pointwise composites as faces and
-- coh2Layer-cubeP carries it — base and fiber together — along the
-- ∙Πapp cells to the goal's applied composites.
Coh2LayerSucT n p k e D E₁ E₂ E₃ E₄ q Hq r Hr s Hs ε ω θ d l θ' = SquareP
    (λ i j → GDom (painting n p k e D E₁
       (restr-frame n p k e (D ∷ E₁) 0 tt θ'
          (coh2-frame (n +1) p (k +1) e
             ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
             (q +1) Hq (r +1) Hr (s +1) Hs ε ω θ d i j))))
    (λ j → coh-layer (n +1) p k e
             (((D ∷ E₁) ∷ E₂) ∷ E₃) q Hq r Hr ε ω
             (restr-frame (n +3) p (k +3) e
                ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) (s +1)
                (le-up s (k +1) (le-up s k
                   (le-trans s r k Hs
                      (le-trans r q k Hr Hq)))) θ d)
             (restr-layer (n +3) p (k +2) e
                ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) s
                (le-up s (k +1) (le-up s k
                   (le-trans s r k Hs
                      (le-trans r q k Hr Hq)))) θ d l) j θ')
    (λ j → restr-layer (n +1) p k e ((D ∷ E₁) ∷ E₂) s
             (le-trans s r k Hs (le-trans r q k Hr Hq)) θ
             (coh-frame (n +2) p (k +2) e
                ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
                (q +2) Hq (r +2) Hr ε ω d j)
             (coh-layer (n +2) p (k +1) e
                ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
                (q +1) Hq (r +1) Hr ε ω d l j) θ')
    (λ i → compPathP
       {P = λ x → GDom (layer (n +1) p k e (D ∷ E₁) x)}
       (λ i' → restr-layer (n +1) p k e ((D ∷ E₁) ∷ E₂) q Hq ε
                 (coh-frame (n +2) p (k +2)
                    e ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) (r +1)
                    (le-trans r q (k +1) Hr
                       (le-up q k Hq)) (s +1) Hs ω θ d i')
                 (coh-layer (n +2) p (k +1) e
                    ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) r
                    (le-trans r q (k +1) Hr
                       (le-up q k Hq)) s Hs ω θ d l i'))
       (coh-layer (n +1) p k e
          (((D ∷ E₁) ∷ E₂) ∷ E₃) q Hq s
          (le-trans s r q Hs Hr) ε θ
          (restr-frame (n +3) p (k +3) e
             ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) (r +2)
             (le-trans r q (k +1) Hr (le-up q k Hq)) ω d)
          (restr-layer (n +3) p (k +2) e
             ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) (r +1)
             (le-trans r q (k +1) Hr (le-up q k Hq)) ω d l)) i θ')
    (λ i → compPathP
       {P = λ x → GDom (layer (n +1) p k e (D ∷ E₁) x)}
       (λ i' → restr-layer (n +1) p k e ((D ∷ E₁) ∷ E₂) r
                 (le-trans r q k Hr Hq) ω
                 (coh-frame (n +2) p (k +2)
                    e ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) (q +2) Hq (s +1)
                    (le-up s q (le-trans s r q Hs Hr)) ε θ d i')
                 (coh-layer (n +2) p (k +1) e
                    ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) (q +1) Hq s
                    (le-up s q (le-trans s r q Hs Hr)) ε θ d l i'))
       (coh-layer (n +1) p k e (((D ∷ E₁) ∷ E₂) ∷ E₃) r
          (le-trans r q k Hr Hq) s Hs ω θ
          (restr-frame (n +3) p (k +3) e
             ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) (q +3) Hq ε d)
          (restr-layer (n +3) p (k +2) e
             ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) (q +2) Hq ε d l)) i θ')

coh2-layer zero    p k ()
coh2-layer (n +1) p k e ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) q Hq r Hr s Hs
           ε ω θ d l i j θ' =
  coh2-layer-suc n p k e D E₁ E₂ E₃ E₄ q Hq r Hr s Hs ε ω θ d l θ' i j

coh2-layer-suc n p k e D E₁ E₂ E₃ E₄ q Hq r Hr s Hs ε ω θ d l θ' =
  coh2Layer-cubeP
       {X = GDom (frame n p k e D)} {P = P'}
       {Y = GDom (frame (n +1) p (k +1) e P₁)} {S = S'}
       {Z = GDom (frame (n +2) p (k +2) e P₂)} {T̃ = S̃}
       {T = arity}
       (isGroupoidDom (frame n p k e D)) Rθ θ' rfq rfr rfs Fq Fr Fs
       w⁺ r̂fr r̂fs r̂fsq r̂fsr r̂ss F̂r Ĝs F̂sq F̂sr
       (λ z → coh-frame n p k e P₂ q Hq 0 tt ε θ' z)
       (λ z → coh-frame n p k e P₂ r H₂ 0 tt ω θ' z)
       (λ z → coh-frame n p k e P₂ s HsB 0 tt θ θ' z)
       (λ z → coh-frame n p k e P₂ q Hq r Hr ε ω z)
       (λ z c → coh-painting n p k e P₂ E₃ q Hq r Hr ε ω z c)
       (λ z → coh-frame n p k e P₂ q Hq s HsHr ε θ z)
       (λ z c → coh-painting n p k e P₂ E₃ q Hq s HsHr ε θ z c)
       (λ z → coh-frame n p k e P₂ r H₂ s Hs ω θ z)
       (λ z c → coh-painting n p k e P₂ E₃ r H₂ s Hs ω θ z c)
       κ' cS̃ κ'C c̃C κ'E c̃E C2f' D2f' E1f' C2K D2K sC sD D2C D1E1
       (coh-frame (n +1) p (k +1) e P₃ r H₁ s Hs ω θ b')
       (coh-frame (n +1) p (k +1) e P₃ (q +1) Hq s Hs↑ ε θ b')
       (coh-frame (n +1) p (k +1) e P₃ (q +1) Hq (r +1) Hr ε ω b') E1K
       (coh-frame (n +1) p (k +1) e P₃ (q +1) Hq (s +1) HsHr ε θ dRf')
       (coh-frame (n +1) p (k +1) e P₃ (r +1)
          (le-trans (r +1) (q +1) (k +1) Hr Hq) (s +1) Hs ω θ dEf')
       (coh-painting (n +1) p (k +1) e P₃ E₄ r H₁ s Hs ω θ b' (l θ'))
       (coh-painting (n +1) p (k +1) e P₃ E₄ (q +1) Hq s Hs↑ ε θ b' (l θ'))
       (coh-painting (n +1) p (k +1) e P₃ E₄ (q +1) Hq (r +1) Hr ε ω b' (l θ'))
       sqK sqE1 sqC2' sqD2' sqC sqD
       fillK fillPE1 fillPC2s' fillPD2s' fillC fillD B₀
       (coh2-painting n p k e P₃ E₄ q Hq r Hr s Hs ε ω θ b' (l θ'))
       (λ ii jj → w (E2 ii jj))
       (λ o ii → ΠC.csq (~ o) ii)
       (λ o ii → ΠD.csq (~ o) ii)
       (λ o ii → ΠC.csqP (~ o) ii)
       (λ o ii → ΠD.csqP (~ o) ii) where
  P₁ = (D ∷ E₁)
  P₂ = ((D ∷ E₁) ∷ E₂)
  P₃ = (((D ∷ E₁) ∷ E₂) ∷ E₃)
  P₄ = ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
  H₁ = le-trans r q (k +1) Hr (le-up q k Hq)
  H₂ = le-trans r q k Hr Hq
  HsHr = le-trans s r q Hs Hr
  HsB = le-trans s r k Hs H₂
  HsS = le-up s (k +1) (le-up s k HsB)
  -- families and restriction maps
  P' : GDom (frame n p k e D) → Set
  P' = λ x → GDom (painting n p k e D E₁ x)
  S' : GDom (frame (n +1) p (k +1) e P₁) → Set
  S' = λ y → GDom (painting (n +1) p (k +1) e P₁ E₂ y)
  S̃ : GDom (frame (n +2) p (k +2) e P₂) → Set
  S̃ = λ z → GDom (painting (n +2) p (k +2) e P₂ E₃ z)
  w = λ y → restr-frame n p k e P₁ 0 tt θ' y
  rfq = λ y → restr-frame n p k e P₁ q Hq ε y
  rfr = λ y → restr-frame n p k e P₁ r H₂ ω y
  rfs = λ y → restr-frame n p k e P₁ s HsB θ y
  Fq = λ y c → restr-painting n p k e P₁ E₂ q Hq ε y c
  Fr = λ y c → restr-painting n p k e P₁ E₂ r H₂ ω y c
  Fs = λ y c → restr-painting n p k e P₁ E₂ s HsB θ y c
  w⁺ = λ z → restr-frame (n +1) p (k +1) e P₂ 0 tt θ' z
  -- the premise's base square and the goal's
  b' = restr-frame (n +3) p (k +3) e P₄ 0 tt θ' d
  B₀ = coh2-frame n p k e P₃ q Hq r Hr s Hs ε ω θ b'
  E2 = coh2-frame (n +1) p (k +1) e P₄ (q +1) Hq (r +1) Hr (s +1) Hs ε ω θ d
  -- the K face: pack, filler, conjugation
  dSf = restr-frame (n +3) p (k +3) e P₄ (s +1) HsS θ d
  dSl = restr-layer (n +3) p (k +2) e P₄ s HsS θ d l
  bK = restr-frame (n +2) p (k +2) e P₃ 0 tt θ' dSf
  E1K = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq (r +1) Hr ε ω dSf
  C2K = coh-frame (n +1) p (k +1) e P₃ r H₁ 0 tt ω θ' dSf
  D2K = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq 0 tt ε θ' dSf
  dRK = restr-frame (n +2) p (k +2) e P₃ (r +1) H₁ ω dSf
  dEK = restr-frame (n +2) p (k +2) e P₃ (q +2) Hq ε dSf
  C1K = coh-frame n p k e P₂ q Hq 0 tt ε θ' dRK
  D1K = coh-frame n p k e P₂ r H₂ 0 tt ω θ' dEK
  KK = coh-frame n p k e P₂ q Hq r Hr ε ω bK
  m1K = restr-frame (n +1) p (k +1) e P₂ r H₁ ω bK
  m2K = restr-frame (n +1) p (k +1) e P₂ 0 tt θ' dRK
  n1K = restr-frame (n +1) p (k +1) e P₂ (q +1) Hq ε bK
  n2K = restr-frame (n +1) p (k +1) e P₂ 0 tt θ' dEK
  aLK = restr-painting (n +1) p (k +1) e P₂ E₃ r H₁ ω bK (dSl θ')
  aRK = restr-painting (n +1) p (k +1) e P₂ E₃ (q +1) Hq ε bK (dSl θ')
  HCPK = coh-painting n p k e P₂ E₃ q Hq r Hr ε ω bK (dSl θ')
  sqK = coh2-frame n p k e P₃ q Hq r Hr 0 tt ε ω θ' dSf
  fillK = cohLayer-fillP {P = P'} {S2 = S'} {S3 = S'} {rf0 = w}
    {rfF = rfq} {rfG = rfr} {F = Fq} {G = Fr} {E1 = E1K}
    {m1 = m1K} {m2 = m2K} {C2 = C2K} {n1 = n1K} {n2 = n2K} {D2 = D2K}
    {C1 = C1K} {D1 = D1K} {K = KK} {aL = aLK} {aR = aRK} HCPK sqK
  κ' = coh-frame (n +2) p (k +2) e P₄ s HsS 0 tt θ θ' d
  cS̃ = restr-painting (n +2) p (k +2) e P₃ E₄ s HsS θ b' (l θ')
  -- the E1 face: conjugation and transport filler
  E1f' = coh-frame (n +2) p (k +2) e P₄ (q +2) Hq (r +2) Hr ε ω d
  sqE1 = coh2-frame (n +1) p (k +1) e P₄ (q +1) Hq (r +1) Hr 0 tt ε ω θ' d
  dRf' = restr-frame (n +3) p (k +3) e P₄ (r +2) H₁ ω d
  dEf' = restr-frame (n +3) p (k +3) e P₄ (q +3) Hq ε d
  bC = restr-frame (n +2) p (k +2) e P₃ 0 tt θ' dRf'
  bD = restr-frame (n +2) p (k +2) e P₃ 0 tt θ' dEf'
  κ'C = coh-frame (n +2) p (k +2) e P₄ (r +1) H₁ 0 tt ω θ' d
  c̃C = restr-painting (n +2) p (k +2) e P₃ E₄ (r +1) H₁ ω b' (l θ')
  κ'E = coh-frame (n +2) p (k +2) e P₄ (q +2) Hq 0 tt ε θ' d
  c̃E = restr-painting (n +2) p (k +2) e P₃ E₄ (q +2) Hq ε b' (l θ')
  D2C = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq 0 tt ε θ' dRf'
  D1E1 = coh-frame (n +1) p (k +1) e P₃ (r +1)
           (le-trans (r +1) (q +1) (k +1) Hr Hq) 0 tt ω θ' dEf'
  fillPE1 = cohLayer-fillP {P = S'} {S2 = S̃} {S3 = S̃} {rf0 = w⁺}
    {rfF = λ z → restr-frame (n +1) p (k +1) e P₂ (q +1) Hq ε z}
    {rfG = λ z → restr-frame (n +1) p (k +1) e P₂ (r +1)
                   (le-trans (r +1) (q +1) (k +1) Hr Hq) ω z}
    {F = λ z c → restr-painting (n +1) p (k +1) e P₂ E₃ (q +1) Hq
                   ε z c}
    {G = λ z c → restr-painting (n +1) p (k +1) e P₂ E₃ (r +1)
                   (le-trans (r +1) (q +1) (k +1) Hr Hq) ω z c}
    {E1 = E1f'}
    {m1 = restr-frame (n +2) p (k +2) e P₃ (r +1) H₁ ω b'}
    {m2 = bC}
    {C2 = κ'C}
    {n1 = restr-frame (n +2) p (k +2) e P₃ (q +2) Hq ε b'}
    {n2 = bD}
    {D2 = κ'E}
    {C1 = D2C}
    {D1 = D1E1}
    {K = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq (r +1) Hr ε ω b'}
    {aL = c̃C}
    {aR = c̃E}
    (coh-painting (n +1) p (k +1) e P₃ E₄ (q +1) Hq (r +1) Hr ε ω b' (l θ')) sqE1
  -- shared (suc n)-level maps and values
  r̂fr = λ z → restr-frame (n +1) p (k +1) e P₂ r H₁ ω z
  r̂fs = λ z → restr-frame (n +1) p (k +1) e P₂ s
                (le-trans s r (k +1) Hs H₁) θ z
  r̂fsq = λ z → restr-frame (n +1) p (k +1) e P₂ (q +1) Hq ε z
  r̂fsr = λ z → restr-frame (n +1) p (k +1) e P₂ (r +1)
                 (le-trans (r +1) (q +1) (k +1) Hr Hq) ω z
  r̂ss = λ z → restr-frame (n +1) p (k +1) e P₂ (s +1) HsB θ z
  F̂r = λ z c → restr-painting (n +1) p (k +1) e P₂ E₃ r H₁ ω z c
  Ĝs = λ z c → restr-painting (n +1) p (k +1) e P₂ E₃ s
                 (le-trans s r (k +1) Hs H₁) θ z c
  F̂sq = λ z c → restr-painting (n +1) p (k +1) e P₂ E₃ (q +1) Hq ε z c
  F̂sr = λ z c → restr-painting (n +1) p (k +1) e P₂ E₃ (r +1)
                  (le-trans (r +1) (q +1) (k +1) Hr Hq) ω z c
  lRC = subst S̃ κ'C c̃C
  lED = subst S̃ κ'E c̃E
  -- the C face
  sC = coh-frame (n +1) p (k +1) e P₃ s (le-trans s r (k +1) Hs H₁) 0 tt θ θ' dRf'
  C2f' = coh-frame (n +2) p (k +2) e P₄ (r +1) H₁ (s +1) Hs ω θ d
  sqC2' = coh2-frame (n +1) p (k +1) e P₄ r H₁ s Hs 0 tt ω θ θ' d
  XC = Ĝs bC lRC
  aRC = F̂sq bC lRC
  fillPC2s' = cohLayer-fillP {P = S'} {S2 = S̃} {S3 = S̃} {rf0 = w⁺}
    {rfF = r̂fr} {rfG = r̂fs} {F = F̂r} {G = Ĝs}
    {E1 = C2f'}
    {m1 = restr-frame (n +2) p (k +2) e P₃ s HsS θ b'}
    {m2 = bK}
    {C2 = κ'}
    {n1 = restr-frame (n +2) p (k +2) e P₃ (r +1) H₁ ω b'}
    {n2 = bC}
    {D2 = κ'C}
    {C1 = C2K}
    {D1 = sC}
    {K = coh-frame (n +1) p (k +1) e P₃ r H₁ s Hs ω θ b'}
    {aL = cS̃}
    {aR = c̃C}
    (coh-painting (n +1) p (k +1) e P₃ E₄ r H₁ s Hs ω θ b' (l θ')) sqC2'
  dRC = restr-frame (n +2) p (k +2) e P₃ (s +1)
          (le-trans s q (k +1) HsHr (le-up q k Hq)) θ dRf'
  dEC = restr-frame (n +2) p (k +2) e P₃ (q +2) Hq ε dRf'
  sqC = coh2-frame n p k e P₃ q Hq s HsHr 0 tt ε θ θ' dRf'
  fillC = cohLayer-fillP {P = P'} {S2 = S'} {S3 = S'} {rf0 = w}
    {rfF = rfq} {rfG = rfs} {F = Fq} {G = Fs}
    {E1 = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq (s +1) HsHr ε θ
            dRf'}
    {m1 = restr-frame (n +1) p (k +1) e P₂ s
            (le-trans s q (k +1) HsHr (le-up q k Hq)) θ bC}
    {m2 = restr-frame (n +1) p (k +1) e P₂ 0 tt θ' dRC}
    {C2 = sC}
    {n1 = restr-frame (n +1) p (k +1) e P₂ (q +1) Hq ε bC}
    {n2 = restr-frame (n +1) p (k +1) e P₂ 0 tt θ' dEC}
    {D2 = D2C}
    {C1 = coh-frame n p k e P₂ q Hq 0 tt ε θ' dRC}
    {D1 = coh-frame n p k e P₂ s HsB 0 tt θ θ' dEC}
    {K = coh-frame n p k e P₂ q Hq s HsHr ε θ bC}
    {aL = XC}
    {aR = aRC}
    (coh-painting n p k e P₂ E₃ q Hq s HsHr ε θ bC lRC) sqC
  -- junction cells of the C face
  -- the D face
  sD = coh-frame (n +1) p (k +1) e P₃ s (le-trans s r (k +1) Hs H₁) 0 tt θ θ' dEf'
  Hs↑ = le-up s q HsHr
  D2f' = coh-frame (n +2) p (k +2) e P₄ (q +2) Hq (s +1) Hs↑ ε θ d
  sqD2' = coh2-frame (n +1) p (k +1) e P₄ (q +1) Hq s Hs↑ 0 tt ε θ θ' d
  XD = Ĝs bD lED
  aRD = F̂sr bD lED
  fillPD2s' = cohLayer-fillP {P = S'} {S2 = S̃} {S3 = S̃} {rf0 = w⁺}
    {rfF = r̂fsq} {rfG = r̂fs} {F = F̂sq} {G = Ĝs}
    {E1 = D2f'}
    {m1 = restr-frame (n +2) p (k +2) e P₃ s HsS θ b'}
    {m2 = bK}
    {C2 = κ'}
    {n1 = restr-frame (n +2) p (k +2) e P₃ (q +2) Hq ε b'}
    {n2 = bD}
    {D2 = κ'E}
    {C1 = D2K}
    {D1 = sD}
    {K = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq s Hs↑ ε θ b'}
    {aL = cS̃}
    {aR = c̃E}
    (coh-painting (n +1) p (k +1) e P₃ E₄ (q +1) Hq s Hs↑ ε θ b' (l θ')) sqD2'
  dRD = restr-frame (n +2) p (k +2) e P₃ (s +1)
          (le-trans s r (k +1) Hs H₁) θ dEf'
  dED = restr-frame (n +2) p (k +2) e P₃ (r +2) H₂ ω dEf'
  sqD = coh2-frame n p k e P₃ r H₂ s Hs 0 tt ω θ θ' dEf'
  fillD = cohLayer-fillP {P = P'} {S2 = S'} {S3 = S'} {rf0 = w}
    {rfF = rfr} {rfG = rfs} {F = Fr} {G = Fs}
    {E1 = coh-frame (n +1) p (k +1) e P₃ (r +1)
            (le-trans (r +1) (q +1) (k +1) Hr Hq) (s +1) Hs ω θ dEf'}
    {m1 = restr-frame (n +1) p (k +1) e P₂ s
            (le-trans s r (k +1) Hs H₁) θ bD}
    {m2 = restr-frame (n +1) p (k +1) e P₂ 0 tt θ' dRD}
    {C2 = sD}
    {n1 = restr-frame (n +1) p (k +1) e P₂ (r +1)
            (le-trans (r +1) (q +1) (k +1) Hr Hq) ω bD}
    {n2 = restr-frame (n +1) p (k +1) e P₂ 0 tt θ' dED}
    {D2 = D1E1}
    {C1 = coh-frame n p k e P₂ r H₂ 0 tt ω θ' dRD}
    {D1 = coh-frame n p k e P₂ s HsB 0 tt θ θ' dED}
    {K = coh-frame n p k e P₂ r H₂ s Hs ω θ bD}
    {aL = XD}
    {aR = aRD}
    (coh-painting n p k e P₂ E₃ r H₂ s Hs ω θ bD lED) sqD
  -- junction cells of the D face
  -- the goal's composite-face factors, their pointwise composites
  -- (the cube's j-faces), and the ∙Πapp correction cells
  dRl' = restr-layer (n +3) p (k +2) e P₄ (r +1) H₁ ω d l
  dEl' = restr-layer (n +3) p (k +2) e P₄ (q +2) Hq ε d l
  pC = cong r̂fsq C2f'
  qC = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq (s +1) HsHr ε θ dRf'
  βC = coh-layer (n +1) p k e P₃ q Hq s HsHr ε θ dRf' dRl'
  pD = cong r̂fsr D2f'
  qD = coh-frame (n +1) p (k +1) e P₃ (r +1)
         (le-trans (r +1) (q +1) (k +1) Hr Hq) (s +1) Hs ω θ dEf'
  βD = coh-layer (n +1) p k e P₃ r H₂ s Hs ω θ dEf' dEl'
  Rθ = λ y t → restr-frame n p k e P₁ 0 tt t y
  module ΠC = ∙Πapp {P = P'} Rθ pC qC
    (λ ii → restr-layer (n +1) p k e P₂ q Hq ε (C2f' ii)
              (coh-layer (n +2) p (k +1) e P₄ r H₁ s Hs ω θ d l ii)) βC θ'
  module ΠD = ∙Πapp {P = P'} Rθ pD qD
    (λ ii → restr-layer (n +1) p k e P₂ r H₂ ω (D2f' ii)
              (coh-layer (n +2) p (k +1) e P₄ (q +1) Hq s
                 Hs↑ ε θ d l ii)) βD θ'

-- The painting 2-coherence. The s = 0 case is the filler of the layer
-- coherence's square composition; the s, r, q ≥ 1 case at suc k pairs
-- the layer 2-coherence with the recursive painting 2-coherence.
coh2-painting n p k e (((D ∷ E₁) ∷ E₂) ∷ E₃) E q Hq r Hr zero Hs ε ω θ d (l , c) =
  cohLayer-fillP
    {P = λ x → GDom (painting n p k e D E₁ x)}
    {S2 = λ m → GDom (painting (n +1) p (k +1) e P₁ E₂ m)}
    {S3 = λ m → GDom (painting (n +1) p (k +1) e P₁ E₂ m)}
    {rf0 = λ x → restr-frame n p k e P₁ 0 tt θ x}
    {rfF = λ m → restr-frame n p k e P₁ q Hq ε m}
    {rfG = λ m → restr-frame n p k e P₁ r H₂ ω m}
    {F = λ m c → restr-painting n p k e P₁ E₂ q Hq ε m c}
    {G = λ m c → restr-painting n p k e P₁ E₂ r H₂ ω m c}
    {E1 = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq (r +1) Hr ε ω d}
    {m1 = restr-frame (n +1) p (k +1) e P₂ r H₁ ω (b θ)}
    {m2 = restr-frame (n +1) p (k +1) e P₂ 0 tt θ dR}
    {C2 = coh-frame (n +1) p (k +1) e P₃ r H₁ 0 tt ω θ d}
    {n1 = restr-frame (n +1) p (k +1) e P₂ (q +1) Hq ε (b θ)}
    {n2 = restr-frame (n +1) p (k +1) e P₂ 0 tt θ dE}
    {D2 = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq 0 tt ε θ d}
    {C1 = coh-frame n p k e P₂ q Hq 0 tt ε θ dR}
    {D1 = coh-frame n p k e P₂ r H₂ 0 tt ω θ dE}
    {K = coh-frame n p k e P₂ q Hq r Hr ε ω (b θ)}
    {aL = restr-painting (n +1) p (k +1) e P₂ E₃ r H₁ ω (b θ) (l θ)}
    {aR = restr-painting (n +1) p (k +1) e P₂ E₃ (q +1) Hq ε (b θ) (l θ)}
    (coh-painting n p k e P₂ E₃ q Hq r Hr ε ω (b θ) (l θ))
    (coh2-frame n p k e P₃ q Hq r Hr 0 tt ε ω θ d) where
  P₁ = (D ∷ E₁)
  P₂ = ((D ∷ E₁) ∷ E₂)
  P₃ = (((D ∷ E₁) ∷ E₂) ∷ E₃)
  H₁ = le-trans r q (k +1) Hr (le-up q k Hq)
  H₂ = le-trans r q k Hr Hq
  dR = restr-frame (n +2) p (k +2) e P₃ (r +1) H₁ ω d
  dE = restr-frame (n +2) p (k +2) e P₃ (q +2) Hq ε d
  b : (θ : arity) → GDom (frame (n +2) p (k +2) e P₂)
  b θ = restr-frame (n +2) p (k +2) e P₃ 0 tt θ d
coh2-painting n p k e D E q Hq zero    Hr (s +1) ()
coh2-painting n p k e D E zero    Hq (r +1) ()
coh2-painting n p zero    e D E (q +1) ()
coh2-painting n p (k +1) e (((D ∷ E₁) ∷ E₂) ∷ E₃) E (q +1) Hq (r +1)
              Hr (s +1) Hs ε ω θ d (l , c) i j =
  Σ≡hex.Dep.hexᵈ
    {A = GDom (frame n p (k +1) e D)}
    {B = λ d' → GDom (layer n p k e D d')}
    (λ i' → restr-frame n p (k +1) e (D ∷ E₁) (q +1) Hq ε (C2f i'))
    (coh-frame n p (k +1) e ((D ∷ E₁) ∷ E₂) (q +1) Hq (s +1) HsHr ε θ dRf)
    (λ i' → restr-layer n p k e (D ∷ E₁) q Hq ε (C2f i') (C2s i'))
    (coh-layer n p k e ((D ∷ E₁) ∷ E₂) q Hq s HsHr ε θ dRf dRl)
    (λ i' → restr-frame n p (k +1) e (D ∷ E₁) (r +1) H₂ ω (D2f i'))
    (coh-frame n p (k +1) e ((D ∷ E₁) ∷ E₂) (r +1) H₂ (s +1) Hs ω θ dEf)
    (λ i' → restr-layer n p k e (D ∷ E₁) r H₂ ω (D2f i') (D2s i'))
    (coh-layer n p k e ((D ∷ E₁) ∷ E₂) r H₂ s Hs ω θ dEf dEl)
    (coh-frame n p (k +1) e ((D ∷ E₁) ∷ E₂) (q +1) Hq (r +1) Hr ε ω dSf)
    (coh-layer n p k e ((D ∷ E₁) ∷ E₂) q Hq r Hr ε ω dSf dSl)
    (λ i' → restr-frame n p (k +1) e (D ∷ E₁) (s +1) HsB θ (E1f i'))
    (λ i' → restr-layer n p k e (D ∷ E₁) s HsB θ (E1f i') (E1s i'))
    (coh2-frame n p (k +1) e (((D ∷ E₁) ∷ E₂) ∷ E₃) (q +1) Hq (r +1) Hr (s +1) Hs ε ω θ d)
    (coh2-layer n p k e (((D ∷ E₁) ∷ E₂) ∷ E₃) q Hq r Hr s Hs ε ω θ d l)
    {M = λ x → GDom (painting n (p +1) k e D E₁ x)}
    (λ i' → restr-painting n (p +1) k e (D ∷ E₁) E₂ q Hq ε (C2f i' , C2s i') (C2c i'))
    (coh-painting n (p +1) k e ((D ∷ E₁) ∷ E₂) E₃ q Hq s HsHr ε θ (dRf , dRl) dRc)
    (λ i' → restr-painting n (p +1) k e (D ∷ E₁) E₂ r H₂ ω (D2f i' , D2s i') (D2c i'))
    (coh-painting n (p +1) k e ((D ∷ E₁) ∷ E₂) E₃ r H₂ s Hs ω θ (dEf , dEl) dEc)
    (coh-painting n (p +1) k e ((D ∷ E₁) ∷ E₂) E₃ q Hq r Hr ε ω (dSf , dSl) dSc)
    (λ i' → restr-painting n (p +1) k e (D ∷ E₁) E₂ s HsB θ (E1f i' , E1s i') (E1c i'))
    (coh2-painting n (p +1) k e (((D ∷ E₁) ∷ E₂) ∷ E₃) E q Hq r Hr s Hs ε ω θ (d , l) c)
    i j where
  PP = (((D ∷ E₁) ∷ E₂) ∷ E₃)
  H₁ = le-trans r q (k +1) Hr (le-up q k Hq)
  H₂ = le-trans r q k Hr Hq
  HsHr = le-trans s r q Hs Hr
  Hs↑ = le-up s q (le-trans s r q Hs Hr)
  HsB = le-trans s r k Hs (le-trans r q k Hr Hq)
  HsS = le-up s (k +1) (le-up s k HsB)
  C2f = coh-frame (n +1) p (k +2) e PP (r +1) H₁ (s +1) Hs ω θ d
  C2s = coh-layer (n +1) p (k +1) e PP r H₁ s Hs ω θ d l
  C2c = coh-painting (n +1) (p +1) (k +1) e PP E r H₁ s Hs ω θ (d , l) c
  D2f = coh-frame (n +1) p (k +2) e PP (q +2) Hq (s +1) Hs↑ ε θ d
  D2s = coh-layer (n +1) p (k +1) e PP (q +1) Hq s Hs↑ ε θ d l
  D2c = coh-painting (n +1) (p +1) (k +1) e PP E (q +1) Hq s Hs↑ ε θ (d , l) c
  E1f = coh-frame (n +1) p (k +2) e PP (q +2) Hq (r +2) Hr ε ω d
  E1s = coh-layer (n +1) p (k +1) e PP (q +1) Hq (r +1) Hr ε ω d l
  E1c = coh-painting (n +1) (p +1) (k +1) e PP E (q +1) Hq (r +1) Hr ε ω (d , l) c
  dRf = restr-frame (n +2) p (k +3) e PP (r +2) H₁ ω d
  dRl = restr-layer (n +2) p (k +2) e PP (r +1) H₁ ω d l
  dRc = restr-painting (n +2) (p +1) (k +2) e PP E (r +1) H₁ ω (d , l) c
  dEf = restr-frame (n +2) p (k +3) e PP (q +3) Hq ε d
  dEl = restr-layer (n +2) p (k +2) e PP (q +2) Hq ε d l
  dEc = restr-painting (n +2) (p +1) (k +2) e PP E (q +2) Hq ε (d , l) c
  dSf = restr-frame (n +2) p (k +3) e PP (s +1) HsS θ d
  dSl = restr-layer (n +2) p (k +2) e PP s HsS θ d l
  dSc = restr-painting (n +2) (p +1) (k +2) e PP E s HsS θ (d , l) c

------------------------------------------------------------------------
-- The tower
------------------------------------------------------------------------

-- The full frame at dimension n: the one whose index is the length,
-- at the dimension that IS the length.
fullframe : {n : ℕ} (D : Pre n) → HGpd₀
fullframe {n} D = frame n n 0 (eqN-refl n) D

record νGpd→ (n : ℕ) (D : Pre n) : Set₁ where
  coinductive
  constructor _∷ν_
  field
    this : Fil n 0 D
    next : νGpd→ (n +1) (D ∷ this)
open νGpd→ public

νGpds : Set₁
νGpds = νGpd→ 0 tt*
